signature TRANSLATE =
sig
    datatype level = Top 
	       | Inner of {unique: unit ref, parent: level, frame: MipsFrame.frame}
	
    type access
    type exp

    val outermost : level
    val newLevel : {parent: level,
                    name: Temp.label,
                    formals: bool list} -> level
    val formals : level -> access list
    val allocLocal : level -> bool -> access
    val procEntryExit : level*exp->unit
    val getResult:unit -> MipsFrame.frag list

end

structure Translate (*: TRANSLATE *)=
struct

structure T = Tree
structure A = Absyn
structure Frame = MipsFrame
structure Er = ErrorMsg

val fraglist : Frame.frag list ref = ref []

fun getResult () = !fraglist


datatype level = Top 
	       | Inner of {unique: unit ref, parent: level, frame: Frame.frame}
		   
type access = level*Frame.access

val outermost = Top 


fun newLevel ({parent,name,formals}) = Inner({unique = ref (), parent = parent, frame = Frame.newFrame{name=name,formals=formals}})

fun formals (x as Inner({unique, parent,frame})) = 
    let val fs = Frame.formals(frame)
	fun ftoA [] = []
	  | ftoA (a::l) = (x,a)::ftoA(l)
    in
	ftoA(fs)
    end
  | formals (Top) = []

fun allocLocal (x as Inner({unique,parent,frame})) = (fn(escape) => (x, Frame.allocLocal(frame)(escape)))  
  | allocLocal (Top) = fn(escape) => (Top,Frame.InReg(Temp.newtemp())) (*Er.impossible "Cannot allcLocal from Top"*)


exception Error of string

datatype exp = Ex of T.exp
	     | Nx of T.stm
	     | Cx of Temp.label * Temp.label -> T.stm


fun errorExp() = Ex(T.CONST(0))	 
	 
fun seq [] = T.EXP(T.CONST(0))
  | seq [b] = b
  | seq (a::l) = T.SEQ(a,seq(l))
	 
fun unEx(Ex e) = e
  | unEx(Cx g) =
    let
        val r = Temp.newtemp()
        val t = Temp.newlabel() 
	val f = Temp.newlabel()
    in
        T.ESEQ(seq[T.MOVE(T.TEMP r, T.CONST 1),
                   g(t,f),
                   T.LABEL f,
                   T.MOVE(T.TEMP r, T.CONST 0),
                   T.LABEL t],
               T.TEMP r)
    end
  | unEx(Nx s) = T.ESEQ(s, T.CONST 0)

fun unCx(Cx g) = g
  | unCx(Ex(T.CONST 0)) = (fn (t, f) => T.JUMP(T.NAME f, [f]))
  | unCx(Ex(T.CONST _)) = (fn (t, f) => T.JUMP(T.NAME t, [t]))
  | unCx(Ex e) = (fn (t, f) => T.CJUMP(T.NE, e, T.CONST 0, t, f))
  | unCx(Nx s) = raise Error ("Cannot unCx an Nx")

fun unNx(Nx s) = s
  | unNx(Ex e) = T.EXP(e)
  | unNx(Cx g) = 
    let
	val t = Temp.newlabel()
	val f = t
    in
	 T.SEQ(g(t,f), T.LABEL t)
    end


fun nilExp () = Ex(T.CONST 0)

fun intExp (n) = Ex(T.CONST n)

fun stringExp(s) =  
	let 
		val slabel = Temp.newlabel()
		val _ = (fraglist := Frame.STRING(slabel, s)::(!fraglist))
	in 
		Ex (T.NAME (slabel))
	end

fun opExp (left, Absyn.PlusOp, right) = 
	Ex (T.BINOP(T.PLUS, unEx left,unEx right))

  | opExp (left, Absyn.MinusOp, right) = 
	Ex (T.BINOP(T.MINUS, unEx left,unEx right))
	
  | opExp (left, Absyn.TimesOp, right) = 
	Ex (T.BINOP(T.MUL, unEx left,unEx right))

  | opExp (left, Absyn.DivideOp, right) = 
	Ex (T.BINOP(T.DIV, unEx left,unEx right))

  | opExp (left, Absyn.EqOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.EQ,unEx left,unEx right,t,f))

  | opExp (left, Absyn.NeqOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.NE,unEx left,unEx right,t,f))

  | opExp (left, Absyn.LtOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.LT,unEx left,unEx right,t,f))

  
  | opExp (left, Absyn.LeOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.LE,unEx left,unEx right,t,f))


  | opExp (left, Absyn.GtOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.GT,unEx left,unEx right,t,f))


  | opExp (left, Absyn.GeOp, right) = 	
    	Cx (fn(t,f) => T.CJUMP(T.GE,unEx left,unEx right,t,f))

	
fun assignExp(var, exp) =
    let
        val var = unEx var
        val exp = unEx exp
    in
        Nx (T.MOVE (var, exp))
    end

fun whileExp (test, body, break) = 
    let
	val test = unCx test
	val body = unNx body
	val testL = Temp.newlabel()
	val bodyL = Temp.newlabel()
	
    in
	Nx (seq[T.LABEL testL,
		  test(bodyL,break),
		  T.LABEL bodyL,
		  body,
		  T.JUMP (T.NAME testL, [testL]),
		  T.LABEL break])
    end


fun forExp (var, lo, hi, body,break) = 
    let 
        val var = unEx var
        val lo = unEx lo
        val hi = unEx hi
        val body = unNx body
        val bodyL = Temp.newlabel()
        val forL = Temp.newlabel()

    in
	Nx (seq[T.MOVE(var,lo),
		  T.CJUMP(T.LE,var,hi,bodyL,break),
		  T.LABEL bodyL,
		  body,
		  T.CJUMP(T.LT,var,hi,forL,break),
		  T.LABEL forL,
		  T.MOVE(var,T.BINOP(T.PLUS,var,T.CONST 1)),
		  T.JUMP(T.NAME bodyL, [bodyL]),
		  T.LABEL break])
    end


fun ifThenElseExp(test, thenExp, elseExp) = 
    let 
	val condition=unCx test
	val exp1=unEx thenExp
	val exp2=unEx elseExp
	val tlabel=Temp.newlabel()
	val flabel=Temp.newlabel()
	val temp= T.TEMP (Temp.newtemp())
	val join = Temp.newlabel()
		   
    in
	Ex(
	T.ESEQ(seq[condition(tlabel,flabel),
		   T.LABEL tlabel, T.MOVE(temp,exp1), T.JUMP(T.NAME join,[join]), T.LABEL flabel, T.MOVE(temp,exp2), T.LABEL join],
	       temp)
	)
    end
fun ifThenExp(test,thenExp) =
    let 
	val condition = unCx test
	val exp1=unNx thenExp		
	val tlabel=Temp.newlabel()
	val flabel=Temp.newlabel()

    in
	
	Nx(
		seq[condition(tlabel,flabel),T.LABEL tlabel, exp1, T.LABEL flabel]
		)
	end


fun arrayExp(typ, size, init) = 
    let
	val initval= unEx init
	val arraysize=unEx size
	val count = T.TEMP (Temp.newtemp())
	val arraylabel = Temp.newlabel()
	val join=Temp.newlabel()
	val r= T.TEMP (Temp.newtemp())
    in	
		Ex (T.ESEQ(seq[T.MOVE(r, Frame.externalCall("initArray", [arraysize, initval])),
			 T.MOVE(count,T.CONST(0)),
			 T.LABEL arraylabel,
			 T.MOVE(T.MEM(T.BINOP(T.PLUS,r,T.BINOP(T.MUL, count, T.CONST(Frame.wordSize)))),initval),
			 T.MOVE(count, T.BINOP(T.PLUS, count, T.CONST(1))),
			 T.CJUMP(T.LT, count, arraysize, arraylabel, join),
			 T.LABEL join],r))
    end

fun recordExp (fields, recordname,explist) = 
	let
		val fieldlength = length (fields)
		val count = ref 0
		val recordlabel =Temp.newlabel()
		val join =Temp.newlabel()
		val r = T.TEMP (Temp.newtemp())
	in
		Ex (T.ESEQ(seq[T.MOVE(r, Frame.externalCall("malloc", [T.CONST(fieldlength)])),
			 T.LABEL recordlabel,
			 T.MOVE(T.MEM(T.BINOP(T.PLUS,r,T.BINOP(T.MUL, T.CONST(!count), T.CONST(Frame.wordSize)))),(unEx (List.nth(explist, !count)))),
			 T.MOVE(T.CONST (!count), T.BINOP(T.PLUS, T.CONST(count:=(!count+1);!count), T.CONST(1))),
			 T.CJUMP(T.LT, T.CONST(!count), T.CONST(fieldlength), recordlabel, join),
			 T.LABEL join],r))
	end

(*assume static link always at offset 0 of a frame*)
fun getdefFP (Inner(c),Inner(d)) =
    if (#unique c) = (#unique d)
    then T.TEMP(Frame.FP)
    else T.MEM(getdefFP((#parent c),Inner(d)))	
    |getdefFP(Top,Inner e) = T.TEMP(Frame.FP)

    |getdefFP(Inner e, Top) = T.MEM(getdefFP((#parent e),Top))
    |getdefFP(Top,Top) = T.TEMP(Frame.FP)

     

fun simpleVar (access,level) = 
	let
	    val (defLevel,frameAccess) = access	
	in
	    Ex(
	    Frame.exp(frameAccess)(getdefFP(level,defLevel))
	    )
	end


fun subscriptVar (varexp,index) =
    Ex(T.MEM(T.BINOP(T.PLUS,unEx(varexp),T.BINOP(T.MUL,unEx(index),T.CONST(Frame.wordSize)))))
    

fun fieldVar (varexp,index) =
    Ex(T.MEM(T.BINOP(T.PLUS,unEx(varexp),T.CONST(index*Frame.wordSize))))

fun callExp (dlevel,clevel,label,args) = 
    let
	val sl = 
	    let 
		fun getSL (Inner(d),Inner(c)) = if ((#parent d) = Inner(c)) then T.TEMP(Frame.FP)
				  else if #parent d = #parent c then T.MEM(T.TEMP(Frame.FP))
				  else getSL (Inner(d), (#parent c))
		  |getSL(Top,Top) = T.TEMP Frame.FP
		  |getSL(Inner(d),Top) = T.TEMP Frame.FP
		  |getSL(Top,Inner(c)) = getSL (Top, (#parent c))
	    in
		getSL(dlevel,clevel)
	    end							
	val args = map unEx args
	val args' = sl::args
    in
	Ex (T.CALL(T.NAME label, args'))
    end

fun seqExp [] = Ex (T.CONST 0)
  | seqExp (exp :: exps) = Ex (T.ESEQ (unNx exp, unEx (seqExp exps)))

fun breakExp (break)=  Nx (T.JUMP(T.NAME(break), [break]))
    
fun letExp (asslist, body) = 
	let val unexbody = unEx body
		val theexp = case asslist of
		 [] => Ex(unexbody)
		|_ => 
		 let
		   val l =  map(unNx)(asslist) 
	         in
		     Ex(T.ESEQ(seq l,unexbody)) 
		 end 
	in	
		theexp
	end

fun procEntryExit (Top, body) = ErrorMsg.error 1 "Already at top level"
  | procEntryExit (Inner{unique,parent,frame},body) = 
    let
	
	val bodyexp = unEx body
	val newbody = T.MOVE(T.TEMP(Frame.RV), bodyexp)
	val bodystm = seq[Frame.procEntryExit1(frame, newbody)]  
	
(*	val bodystm = Frame.procEntryExit1(frame,unNx(body)) *)
    in
	fraglist := (Frame.PROC{body=bodystm, frame=frame}::(getResult()))
    end


    
end












 
    
