signature MAKEGRAPH = 
sig
    val instrs2graph : Assem.instr list ->
                       Flow.flowgraph * (*Flow.*)Graph.node list
end

structure Makegraph :> MAKEGRAPH =

struct

structure G = Graph
structure A = Assem  

fun instrs2graph instrs =
    let
	(*initilize the graph, node list, and the def,use,move tables*)
        val graph = Graph.newGraph ()
        val nodes = map (fn _ => Graph.newNode graph) instrs
	val initDefTable = G.Table.empty
	val initUseTable = G.Table.empty 
	val initMoveTable = G.Table.empty  

	(*construct the three tables according to the instr*)
	fun constructTable (instr, node, (defT,useT,moveT)) =
	    case instr of 
		A.OPER {assem,dst,src,jump} => (G.Table.enter (defT, node, dst),
						G.Table.enter (useT, node, src),
						G.Table.enter (moveT, node, false))

	      | A.LABEL {assem, lab} => (G.Table.enter (defT, node, []),
					 G.Table.enter (useT, node, []),
					 G.Table.enter (moveT, node, false))

	      | A.MOVE {assem,dst,src} => (G.Table.enter (defT, node, [dst]),
					   G.Table.enter (useT, node, [src]),
					   G.Table.enter (moveT, node, true))
					  
	(*fold the instr*node list to construct the three table*)
	val (defTable, useTable, moveTable) = ListPair.foldl constructTable (initDefTable,initUseTable,initMoveTable) (instrs, nodes)

	(*Building the node list for all the labels*)
	val labelNodeList = List.mapPartial (fn (A.LABEL {assem, lab}, node) => SOME (lab, node)
					      | (_,_) => NONE)
					    (ListPair.zip (instrs, nodes))
			    
	(*get the node for specific label*)
        fun findLabelNode lab =
            case (List.find (fn (l,n) => lab = l) labelNodeList) of
                SOME (_, node) => SOME node
              | NONE => NONE

		


	(*make egdes between nodes*)
	fun makeEdges (instr::instrs, a::(b::c)) =
	    
	    (*For Jump, find the nodes for the label lists and make edges*)
	    (case instr of (A.OPER {assem, dst, src, jump}) =>
			    (case jump of SOME jumpLabs =>
					  app (fn lab => 
						  case (findLabelNode lab) of 
						      SOME node =>
						      (G.mk_edge{from=a, to=node}; makeEdges(instrs,(b::c) ) )
						    | NONE => ()) jumpLabs
					| NONE => (G.mk_edge{from=a, to=b}; makeEdges(instrs,(b::c) )) )
			  (*None Jump, just link to the next node*)
			  | _ => (G.mk_edge {from=a, to=b}; makeEdges(instrs, (b::c) ) ) )
	  |makeEdges(instr::[],n::[]) =
		   (case instr of (A.OPER {assem, dst, src, jump}) =>
			    (case jump of SOME jumpLabs =>
					  app (fn lab => 
						  case (findLabelNode lab) of 
						      SOME node =>
						      (G.mk_edge {from=n, to=node})
						    | NONE => ()) jumpLabs
					| NONE => ()) 
			  (*None Jump, just link to the next node*)
			  | _ => () ) 
  
	  | makeEdges(_,_) =()
	  
	  val ()= makeEdges (instrs,nodes)  
    in
	( (Flow.FGRAPH {control=graph,def=defTable,use=useTable,ismove=moveTable},nodes) )	
    end				
end 
