signature FRAME =
sig

  type frame
  type access
  datatype frag = PROC of {body:Tree.stm, frame:frame} 
		|STRING of Temp.label*string
			   
  val exp : access -> Tree.exp -> Tree.exp
  val FP: Temp.temp
  val wordSize: int
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access
  val externalCall: string * Tree.exp list -> Tree.exp
  val RV : Temp.temp  (*as seen by callee*)
  val procEntryExit1: frame * Tree.stm -> Tree.stm

end
