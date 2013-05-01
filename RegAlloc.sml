signature REG_ALLOC = 
sig
    type allocation = MipsFrame.register Temp.Table.table
    val alloc : Assem.instr list * MipsFrame.frame ->
                Assem.instr list * allocation
                
end

structure RegAlloc : REG_ALLOC = 
struct
structure Frame = MipsFrame
structure T = Tree
type allocation = Frame.register Temp.Table.table
		  
fun alloc(instrs, frame) = 
    let
	val (FGraph, nodes) = Makegraph.instrs2graph(instrs)
	val (IGraph, liveOut) = Liveness.interferenceGraph(FGraph)

	val allocation = Frame.tempMap
	val reglist = Frame.colorregs
		      

	fun getnewinstructions(spilledtemp) = 

	    let
		
		fun gaccess(Frame.InFrame(theaccess))=theaccess
		val taccess = gaccess (Frame.allocLocal(frame)(true))
		val newtemp = Temp.newtemp()

		val storeinstr = (MipsGen.codegen(frame) (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP Frame.FP,T.CONST taccess)), T.TEMP newtemp))) 
		val loadinstr   = (MipsGen.codegen(frame)(T.MOVE(T.TEMP newtemp,T.MEM(T.BINOP(T.PLUS,T.TEMP Frame.FP,T.CONST taccess)))))
				  
		fun newinstrs(Assem.OPER{assem,dst,src,jump }) = 
		    let
			val existsdst = (List.exists (fn(thedst)=>(thedst=spilledtemp)) dst) 
			val existssrc = (List.exists (fn(thesrc)=>(thesrc=spilledtemp)) src)
			val newdstlist= foldr (fn(curtemp,curdstlist)=> if (curtemp=spilledtemp) then [newtemp]@curdstlist else [curtemp]@curdstlist) [] dst
			val newsrclist= foldr (fn(curtemp,cursrclist)=> if (curtemp=spilledtemp) then [newtemp]@cursrclist else [curtemp]@cursrclist) [] src 
			(*val () = if (List.exists (fn(thesrc)=>(thesrc=spilledtemp)) newdstlist) then ErrorMsg.error 0 "DOeSN'T REMOVE FROM SPILLED LIST!!!" else () *)
				
		    in
			
			if  (existsdst andalso existssrc)  then (loadinstr @ [Assem.OPER{assem=assem,dst=newdstlist,src=newsrclist,jump=jump}] @ storeinstr) 
			else ( if existsdst then ([Assem.OPER{assem=assem,dst=newdstlist,src=src,jump=jump}] @ storeinstr) 
			else ( if existssrc then loadinstr @ [Assem.OPER{assem=assem,dst=dst,src=newsrclist,jump=jump}]
			else [Assem.OPER{assem=assem,dst=dst,src=src,jump=jump}])) 
			     
		    end

								  
		  |newinstrs(Assem.LABEL{assem,lab}) = [Assem.LABEL{assem=assem,lab=lab}]

		  |newinstrs(Assem.MOVE{assem,dst,src})  = if (src = spilledtemp andalso dst = spilledtemp) then (loadinstr @ [Assem.MOVE{assem=assem,dst=newtemp,src=newtemp}] @ storeinstr) 
							    else if src = spilledtemp then (loadinstr @ [Assem.MOVE{assem=assem,dst=dst,src=newtemp}]) 
							    else if dst = spilledtemp then ([Assem.MOVE{assem=assem,dst=newtemp,src=src}] @ storeinstr)
							    else [Assem.MOVE{assem=assem,dst=dst,src=src}] 
								 
								 
		val newinstructions' = foldr (fn(curinst,curnewlist)=> newinstrs(curinst) @ curnewlist )        [] instrs
				
	    in
		newinstructions' 
	    end

	val (resultAllocation, spillList) = 
            Color.color {interference = IGraph,
			 initial = allocation,
			 spillCost = (fn node => 1),
			 registers = reglist}
            
	val (fininstrs,finAllocation) = if (List.null(spillList)) then (instrs,resultAllocation)  
					else alloc(getnewinstructions(List.last(spillList)),frame)



    in
	(fininstrs, finAllocation)
    end
end
