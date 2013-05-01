structure main = struct

   structure Tr = Translate
   structure F = MipsFrame
   structure R = RegAlloc
   structure A = Assem

   fun getsome (SOME x) = x

   fun emitproc out (F.PROC{body,frame}) =
       let val _ = print ("emit " ^ Symbol.name(F.name frame) ^ "\n")
	   (*         val _ = Printtree.printtree(out,body); *)
	   val stms = Canon.linearize body
	   (*         val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
           val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	  (* val instrs = foldl (fn(stat,instlist)=>instlist @ (MipsGen.codegen(frame)(stat)) )    []   stms'*)
	   val instrs =   List.concat(map (MipsGen.codegen frame) stms')
 	   val (instrs',allocation) = RegAlloc.alloc(instrs,frame)
	   
           val format0 = Assem.format(Temp.makestring2(allocation))

       in  
	   app (fn i => TextIO.output(out,format0 i)) instrs'
       end

     | emitproc out (F.STRING(lab,s)) = (TextIO.output(out,F.string(lab,s)))
    
   fun withOpenFile fname f = 
       let val out = TextIO.openOut fname
       in (f out before TextIO.closeOut out) 
	  handle e => (TextIO.closeOut out; raise e; ())
       end 

   fun compile filename = 
       let val absyn = Parse.parse filename
           val frags = (FindEscape.findEscape absyn; newSemant.transProg absyn)
       in 
           withOpenFile (filename ^ ".s") 
			(fn out => (app (emitproc out) frags))
       end

end
