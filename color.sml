signature COLOR = 
sig
    
		      
    type allocation = MipsFrame.register Temp.Table.table
		      
    val color : {interference: Liveness.igraph,
		 initial: allocation,
		 spillCost: Graph.node -> int,
		 registers: MipsFrame.register list}
		-> allocation * Temp.temp list
                   
end

structure Color : COLOR =
struct

structure Frame = MipsFrame
structure G = IGraph

structure TempKey = 
struct
type ord_key = Temp.temp
val compare  = Int.compare
end

structure S = SplaySetFn(TempKey)




fun getindex(r,rlist)= 
	let
	    val iref = ref ~1
	     val whatever = List.exists (fn(ther)=>(iref := !iref+1;r=ther)) rlist
	in
		!iref
	end





structure ColorKey = 
struct
type ord_key = MipsFrame.register
val compare =fn(r1,r2)=>Int.compare(getindex(r1,MipsFrame.colorregs),getindex(r2,MipsFrame.colorregs))
end

structure CSet = SplaySetFn(ColorKey)



type allocation = Frame.register Temp.Table.table


fun color {interference = Liveness.IGRAPH {graph, tnode, gtemp, moves}, initial, spillCost, registers} = 
    let

	val ColorSet = CSet.addList(CSet.empty, registers)

	(*the number of colors available*)
	val K = List.length(registers) 

	val nodes = G.nodes(graph)
	val TempSet' = S.addList(S.empty, (map gtemp (nodes)))
	val TempSet = S.filter (fn t => case Temp.Table.look(initial,t) of SOME(x) => false |NONE => true  ) TempSet'

	(* nodes that has less then K neighbours*)
	fun LowDegreeNodes (TempSet) = S.filter (fn n => List.length(G.adj(tnode(n))) < K) TempSet
	(* nodes that has more then K neighbours*)
	fun HighDegreeNodes (TempSet) = S.filter (fn n => List.length(G.adj(tnode(n))) >= K)TempSet

	(*TODO*)
	fun spill(spillednode,table) = (ErrorMsg.error 0 "cannot color; rewrite your program" ;([],table,[spillednode]))

	(*Using list to represent the stack*)
	val SelectStack = []

	fun buildStack (TempSet,stack,table) =
	    let
		val Lnodes = LowDegreeNodes(TempSet)
		val Hnodes = HighDegreeNodes(TempSet)
	    in
		if (S.isEmpty(Lnodes) andalso S.isEmpty(Hnodes)) 
		then (stack,table,[])
		else 
		    (if S.isEmpty(Lnodes)
		     then spill(List.last(S.listItems(Hnodes)),table)
		     else
			 let
			     val node  = tnode(List.hd(S.listItems(Lnodes)))
			     val stack' = stack @ [node]
			     val succs = G.succ(node)
			     val preds = G.pred(node)

			     (*Remember the succs & preds for each node before removing them*)
			     val table' = Temp.Table.enter(table, gtemp(node), (succs @ preds))
			     
			     fun RemovePreds (pred::preds,node) = 
				 (G.rm_edge{from=pred,to=node};RemovePreds(preds,node))
			       | RemovePreds ([],_) = ()

			     fun RemoveSuccs (succ::succs,node) = 
				 (G.rm_edge{from=node,to=succ};RemoveSuccs(succs,node))
			       | RemoveSuccs ([],_) = ()
						      
			     (*val () = RemovePreds (preds,node)*)
			     val () = RemoveSuccs (succs,node)

			     val TempSet' = S.delete(TempSet,gtemp(node))
				      
					  
			 in
			     buildStack(TempSet',stack',table')					  
			 end
		    )

	    end

	val (SelectStack, AdjTable,spillList) = buildStack(TempSet,[],Temp.Table.empty)

	fun colorGraph ([],_,t) = t
	  | colorGraph (stack,popList,colortable) = 
	    let
		val node = List.last(stack)
		val oldTemp = gtemp node

		

	      
		val adjTemps = S.intersection(S.addList(S.empty,map (fn(n)=>gtemp(n)) popList),S.addList(S.empty,map (fn(n)=>gtemp(n)) (valOf(Temp.Table.look(AdjTable,oldTemp) )) ) )
		val adjTempList = S.listItems(adjTemps)
    
		val possColors= foldl (fn(thetemp,curColSet)=>CSet.difference(curColSet,CSet.singleton(valOf(Temp.Table.look(colortable, thetemp)))))  ColorSet adjTempList

		val newColor = List.nth(CSet.listItems(possColors),0) 
		val colortable'= Temp.Table.enter(colortable, oldTemp,newColor)
		val stack' = List.take(stack, length(stack)-1)
		val popList' = popList @ [node]

	    in
		colorGraph(stack',popList',colortable')
	    end


	(*TODO*)
	
    in
	(colorGraph(SelectStack,[],initial),spillList)
    end


end
