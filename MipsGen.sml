signature CODEGEN =
sig
    val codegen : MipsFrame.frame -> Tree.stm -> Assem.instr list
end

structure MipsGen : CODEGEN =
struct

structure A = Assem
structure T = Tree
structure F = MipsFrame

fun int i = if i<0 then (String.concat ["-",Int.toString(0-i)]) else Int.toString i

fun operToString oper = case oper of
			    T.EQ => "beq"
			  | T.NE => "bne"
			  | T.LT => "blt"
			  | T.GT => "bgt"
			  | T.LE => "ble"
			  | T.GE => "bge"
			  | T.ULT => "bltu"
			  | T.ULE => "bleu"
			  | T.UGT => "bgtu"
			  | T.UGE => "bgeu"

val ilist = ref (nil: A.instr list)
fun codegen (frame) (stm : T.stm) : A.instr list = 
    let
	(*val ilist = ref (nil: A.instr list)*)
	val () = ilist:=[]
	fun emit x = (ilist := x::(!ilist))
	fun result (gen) = 
	    let
		val t = Temp.newtemp()
	    in
		gen t;
		t 
	    end

	fun munchStm (T.SEQ(a,b)) = (munchStm a; munchStm b)

	  | munchStm (T.LABEL lab) = 
	    emit(A.LABEL{assem = Symbol.name(lab) ^ ":\n", lab=lab})

	  | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1,T.CONST i)),T.NAME(b))) = 
		
	    emit(Assem.MOVE{assem=("la" ^ Int.toString(i)
				   ^ "(`d0), " ^ Symbol.name(b)),
			    src=Temp.newtemp(),
			    dst=munchExp e1}) 

	  | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i)),e2)) =
 
            emit(A.OPER
		     {assem="sw $`s1, "^ int i ^"($`s0)\n",
		      src=[munchExp e1, munchExp e2],
		      dst=[],jump=NONE})

	  | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i,e1)),e2)) =
	    emit(A.OPER
		     {assem="sw $`s1, "^ int i ^"($`s0)\n",
		      src=[munchExp e1, munchExp e2],
		      dst=[],jump=NONE})


	  | munchStm (T.MOVE(T.MEM(T.CONST i),e2)) =
            emit(A.OPER
		     {assem="sw $`s0, "^ int i ^"($zero)\n",
		      src=[munchExp e2],
		      dst=[], jump=NONE})

	  | munchStm (T.MOVE(T.TEMP i, e2)) =
            emit(A.MOVE
		     {assem="move $`d0, $`s0\n",
		      src=munchExp e2,
		      dst=i})
	  
	  | munchStm (T.MOVE(T.MEM(e1),e2)) =
            emit(A.OPER
		     {assem="sw $`s1, 0($`s0)\n",
		      src=[munchExp e1, munchExp e2],
		      dst=[], jump=NONE})

	  | munchStm (T.JUMP(T.NAME(lab), llst)) =
	    emit(A.OPER
		     {assem = "j " ^ (Symbol.name lab) ^ "\n",
		      src=[], dst=[], jump=SOME[lab]})
	    
	  |munchStm (T.JUMP(e1, llst)) = 
	   emit(A.OPER
		    {assem="j $`s0 \n",src=[munchExp e1], dst=[],
		     jump=SOME(llst)})
	   
	  | munchStm (T.CJUMP(oper, T.CONST i, e1, tlab, flab)) =
	    emit(A.OPER
		     {assem=((operToString (oper)) ^ " $`s0," ^ int i ^ "," ^ Symbol.name(tlab) ^ "\n"),
		      src=[munchExp e1], dst=[], jump=SOME([tlab,flab])})
	    
	  | munchStm (T.CJUMP(oper, e1, T.CONST i, tlab, flab)) =
	    emit(A.OPER
		     {assem=((operToString (oper)) ^ " $`s0," ^ int i ^ "," ^ Symbol.name(tlab) ^ "\n"),
		      src=[munchExp e1], dst=[], jump=SOME([tlab,flab])})

	  | munchStm (T.CJUMP(oper, e1, e2, tlab, flab)) =
	    emit(A.OPER
		     {assem=((operToString (oper)) ^ " $`s0, $`s1," ^ Symbol.name(tlab) ^ "\n"),
		      src=[munchExp e1, munchExp e2], dst=[], jump=SOME([tlab,flab])})

	 (* | munchStm (T.EXP(T.CALL(T.NAME label, args))) =
		let 
	    val () = if (List.length(args)>5 ) 
			then munchStm(T.MOVE(T.TEMP F.SP ,T.BINOP(T.MINUS,T.TEMP F.SP, T.CONST(4*(List.length(args)-4))  )))
		      else munchStm(T.MOVE(T.TEMP F.SP ,T.BINOP(T.MINUS,T.TEMP F.SP, T.CONST(4) )))   

 	in 
           emit(Assem.OPER
		     {assem=(String.concat ["jal " , Symbol.name(label) , "\n"]),
                      src=munchArgs(1,args),
                      dst=F.calldefs, jump=NONE})  
	end
	*)
	  | munchStm (T.EXP exp) = (munchExp exp; ())


	  | munchStm (thetree) = (*Printtree.printtree(TextIO.stdOut,thetree)*)
		( Printtree.printtree(TextIO.stdOut,thetree) ;
	    emit(Assem.OPER
		     {assem="No such munchStm\n",
                      src=[],
                      dst=[],jump=NONE})  )
	  

	and munchArgs(i,args) = 
	    let 

		val ith = List.nth(args,i)

		val ireg = List.nth(F.argregs,i)

		fun emitmem(i,args)=    (*i is the index of the argument in args*)
		let 
		   val stackindex = if i=0 then 0 else i-4
		in  
		    munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST (stackindex*4),T.TEMP F.SP)),ith))
			
		end
		
		fun emitreg(i,args)= 
		    (munchStm (T.MOVE(T.TEMP ireg, ith));ireg)
            in
		
		if (i=List.length(args)-1) then (if i<=4 then [emitreg(i,args)] else (emitmem(i,args);[])  )
	
		else (if (i<=4 andalso i>0) then  emitreg(i,args)::munchArgs(i+1,args)
		else (emitmem(i,args) ;munchArgs(i+1,args)))
            end

	(*and munchArgs(i,[]) = []
	  | munchArgs(i,eh::et) =
            if(i > 0 andalso i < 5)
            then
		let
                    val reg = "`a" ^ int (i-1)
                    val r = List.nth(F.argregs,(i-1))
		in            
                    (emit(A.MOVE{assem="move " ^ reg ^ ", (`s0+0)\n",
				 src=munchExp eh, dst=r});
                     r::munchArgs(i+1,et))
		end       
            else
		munchArgs(i+1,et)*)

	and munchExp(T.ESEQ(stat,exp))=
	    (munchStm stat;munchExp exp)
	
	  |munchExp(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i))) =
           result(fn r => emit(A.OPER
				    {assem="lw $`d0, " ^ int i ^ "($`s0)\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))
	  
	  | munchExp(T.MEM(T.BINOP(T.PLUS,T.CONST i,e1))) =
            result(fn r => emit(A.OPER
				    {assem="lw $`d0, " ^ int i ^ "($`s0)\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.MEM(T.CONST i)) = 
            result(fn r => emit(A.OPER
				    {assem="lw $`d0, " ^ int i ^ "($`r0)\n",
				     src=[], dst=[r], jump=NONE}))

	  | munchExp(T.MEM(e1)) = 
            result(fn r => emit(A.OPER
				    {assem="lw $`d0, 0($`s0)\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) =
            result(fn r => emit(A.OPER
				    {assem="addi $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.PLUS,T.CONST i,e1)) =
            result(fn r => emit(A.OPER
				    {assem="addi $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.PLUS,e1,e2)) =
            result(fn r => emit(A.OPER
				    {assem="add $`d0, $`s0, $`s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.MINUS,e1,e2)) =
            result(fn r => emit(A.OPER
				    {assem="sub $`d0, $`s0, $`s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.MUL,e1,e2)) =
	    result(fn r => emit(A.OPER
				    {assem="mul $`d0, $`s0, $`s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.DIV,e1,e2)) = 
	    result(fn r => emit(A.OPER
				    {assem="div $`d0, $`s0, $`s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.AND,e1,T.CONST i)) =
            result(fn r => emit(A.OPER
				    {assem="andi $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.AND, T.CONST i, e1)) =
            result(fn r => emit(A.OPER
				    {assem="andi $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.AND, e1, e2)) =
            result(fn r => emit(A.OPER
				    {assem="and $`d0, $`s0, `s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.OR, e1, T.CONST i)) =
            result(fn r => emit(A.OPER
				    {assem="ori $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.OR,T.CONST i, e1)) =
            result(fn r => emit(A.OPER
				    {assem="ori $`d0, $`s0, " ^ int i ^ "\n",
				     src=[munchExp e1], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.OR, e1, e2)) =
            result(fn r => emit(A.OPER
				    {assem="or $`d0, $`s0, $`s1\n",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.BINOP(T.LSHIFT, e1, e2)) = 
            result(fn r => emit(A.OPER
				    {assem="sll $`d0, $`s0, $`s1",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

          | munchExp(T.BINOP(T.RSHIFT, e1, e2)) = 
            result(fn r => emit(A.OPER
				    {assem="srl $`d0, $`s0, $`s1",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

          | munchExp(T.BINOP(T.ARSHIFT, e1, e2)) = 
            result(fn r => emit(A.OPER
				    {assem="sra $`d0, $`s0, $`s1",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

          | munchExp(Tree.BINOP(T.XOR, e1, e2)) = 
            result(fn r => emit(A.OPER
				    {assem="xor $`d0, $`s0, $`s1",
				     src=[munchExp e1, munchExp e2], dst=[r], jump=NONE}))

	  | munchExp(T.CONST i) =
	    result(fn r => emit(A.OPER
				    {assem="addi $`d0, $zero, " ^ int i ^ "\n",
				     src=[], dst=[r], jump=NONE}))

	  | munchExp(T.TEMP t) = t

	  | munchExp(T.NAME n) = 
            (*result(fn r =>  emit(A.LABEL{assem=Symbol.name(n) ^ ":\n",lab=n}))*)
		Temp.newtemp()

	 | munchExp (T.CALL(T.NAME label, args)) =
		let

	    fun newname(name) = if (name="print" orelse name="flush" orelse name="getchar" orelse name="ord" orelse name="chr" orelse name="size" orelse name="substring" orelse name="concat"
							orelse name="not" orelse name="exit") then ("tig_" ^ name) else name
	    val thename= newname(Symbol.name (label))

	    val () = if (List.length(args)>5 ) 
			then munchStm(T.MOVE(T.TEMP F.SP ,T.BINOP(T.MINUS,T.TEMP F.SP, T.CONST(4*(List.length(args)-4))  )))
		      else munchStm(T.MOVE(T.TEMP F.SP ,T.BINOP(T.MINUS,T.TEMP F.SP, T.CONST(4) )))   

 	in 
		 (emit(Assem.OPER
		     {assem=(String.concat ["jal " , thename , "\n"]),
                      src= if (List.length(args)<=1) then [] else munchArgs(1,args),
                      dst=[F.RV], jump=NONE})  ; F.RV) 
	end
   
(*	


	  | munchExp ((T.CALL(e, args))) =
            result(fn r => emit(Assem.OPER
		     {assem="jal $`s0\n",
                      src=(munchExp e)::munchArgs(1,args),
                      dst=F.calldefs, jump=NONE})) 

	 
*)
    in

       (ilist:=[]; munchStm(stm);
	rev(!ilist) )
	
	(*let fun returnfunc(treestm)=(munchStm(treestm);!ilist)
	in
	    returnfunc

	end
      *)
 
    end
end
