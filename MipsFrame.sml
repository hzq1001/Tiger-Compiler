structure MipsFrame (*: FRAME*) =
struct

structure T = Tree
structure A = Assem

datatype access = InFrame of int
                | InReg of Temp.temp 

type register = string
type frame = {name: Temp.label, formals: access list, numLocals: int ref}

datatype frag =   PROC of {body:Tree.stm, frame:frame} 
		  |STRING of Temp.label*string
val wordSize = 4

val FP = Temp.newtemp()
val SP = Temp.newtemp()

val RA = Temp.newtemp()
val ZERO = Temp.newtemp()
val RV = Temp.newtemp()

val specialregs = [ZERO, FP, SP, RA, RV]

val argregs' = ["a0", "a1", "a2", "a3"]
val callersaves' = ["t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9","v1"]
val calleesaves' = ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"]
val colorregs =  callersaves' @ calleesaves' @ argregs'
val argregs = map (fn _ => Temp.newtemp()) argregs'
val callersaves = map (fn _ => Temp.newtemp()) callersaves'
val calleesaves = map (fn _ => Temp.newtemp()) calleesaves'

val calldefs = callersaves @ [RA]

val registers = ["zero","fp","sp","ra","v0"] @ argregs' @ callersaves' @ calleesaves'
val registers'= specialregs @ argregs @ callersaves @ calleesaves

val tempMap = foldl (fn ((key, value), table)=> Temp.Table.enter(table, key, value)) Temp.Table.empty (ListPair.zip(registers', registers))


fun exp (InFrame offset) = (fn(fp)=> T.MEM(T.BINOP(T.PLUS,fp,T.CONST(offset))))
  | exp (InReg temp) = (fn(fp)=>T.TEMP(temp))


fun fToA (formal,count) = if formal 
			  then (count := !count + 1; 
				InFrame(wordSize * !count)) 
			  else InReg(Temp.newtemp()) 

fun fsToAs fs = 
    let  val count = ref 0
    in
	case fs of [] => []
		 | (formal::l) => fToA(formal,count)::fsToAs(l)
    end



fun newFrame ({name,formals}) = {name=name, formals = fsToAs formals, numLocals = ref 0}
fun name ({name,formals,numLocals}) = name
fun formals ({name,formals,numLocals}) = formals
fun numLocals ({name,formals,numLocals}) = numLocals
		  
fun allocLocal (f) (true) = 
    let 
	  val numLocals = numLocals f
      in
	  numLocals  := !numLocals + 1;
	  InFrame(0 - !numLocals * wordSize)
      end
    | allocLocal (f) (false) =
      let
	  val numLocals = numLocals f
      in
	  numLocals := !numLocals + 1;
	  InReg(Temp.newtemp())
      end

fun seq [] = T.EXP(T.CONST(0))
  | seq [b] = b
  | seq (a::l) = T.SEQ(a,seq(l))
      
fun externalCall(s,args) =
    T.CALL(T.NAME(Temp.namedlabel ("tig_" ^ s)),args)

fun string (label, str) = 
      ( ".data \n" ^ ".align 4 \n"  ^ (Symbol.name label)  ^ ":\n.word " ^ (Int.toString(String.size(str))) ^ "\n.ascii " ^ str ^ "\n")




fun procEntryExit1 (frame, body) = 
	let 
		val thelabel = #name frame
		val savedregs = calleesaves @ [RA]
 
		val memlocs = map (fn (x) => allocLocal(frame)(true) ) savedregs
		
		val savereginstructions = seq(map (fn(InFrame(memaccess),reg)=>T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP FP,T.CONST memaccess)), T.TEMP reg )) (ListPair.zip(memlocs,savedregs)) )
		val restorereginstructions =  seq(map (fn(InFrame(memaccess),reg)=>T.MOVE(T.TEMP reg, T.MEM(T.BINOP(T.PLUS,T.TEMP FP,T.CONST memaccess)) )) (ListPair.zip(memlocs,savedregs)) )	
		val saveargsinstructions = seq(map (fn(argaccess,argreg)=> case argaccess of  
							InReg reg =>T.MOVE(T.TEMP reg, T.TEMP argreg ) 	
							|InFrame offset => T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP FP,T.CONST offset)), T.TEMP argreg )
			                                        ) (ListPair.zip(formals frame,argregs)) )
		val movesltostack = T.MOVE(T.MEM(T.TEMP SP), T.TEMP FP )
		val updatefp = T.MOVE(T.TEMP FP, T.TEMP SP)
		val updatesp = T.MOVE(T.TEMP SP, T.BINOP(T.MINUS,T.TEMP SP,T.BINOP(T.MUL,T.CONST (4),T.CONST (!(#numLocals frame)) )))
		
		val restoresp = T.MOVE(T.TEMP SP, T.BINOP(T.PLUS,T.TEMP SP,T.BINOP(T.MUL,T.CONST (4),T.CONST (!(#numLocals frame)) )))
		val restorefp = T.MOVE(T.TEMP FP, T.MEM (T.TEMP FP))
		val jumptora = T.JUMP (T.TEMP RA, [] )
	
	in			
 		seq([Tree.LABEL thelabel,movesltostack,updatefp,updatesp ,saveargsinstructions,savereginstructions,body, restorereginstructions,  restoresp,restorefp,jumptora])
	end

fun procEntryExit2 (frame,body) =
    body @ 
    [A.OPER{assem="",
            src=specialregs @ calleesaves,
            dst=[],jump=SOME[]}]

fun procEntryExit3 ({name=name, formals=formals, numLocals=numLocals}:frame, 
                    body : Assem.instr list) =
    {prolog = "PROCEDURE " ^ Symbol.name name ^ "\n",
     body = body,
     epilog = "END " ^ Symbol.name name ^ "\n"}

	
end
