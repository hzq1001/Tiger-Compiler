structure Setmap =
struct


structure Table = IntMapTable(type key = Graph.node
fun getInt(g,n)=n)
type 'a table = 'a Table.table
val empty = Table.empty
val enter = Table.enter
val look= Table.look


end


structure Tempmap =
struct


structure Table = IntMapTable(type key = IGraph.node
fun getInt(g,n)=n)
type 'a table = 'a Table.table
val empty = Table.empty
val enter = Table.enter
val look= Table.look


end


structure Nodemap =
struct

structure Table = IntMapTable(type key = Temp.temp
fun getInt(t)=t)
type 'a table = 'a Table.table
val empty = Table.empty
val enter = Table.enter
val look= Table.look
(*val listItems = Table.listItems*)

end

structure tempKey = 
struct
type ord_key = Temp.temp
val compare = Int.compare
end                            

structure tempSet = SplaySetFn(tempKey)

structure Liveness:
	  sig
	      datatype igraph =
		       IGRAPH of {graph: IGraph.graph,
				  tnode: Temp.temp -> IGraph.node,
				  gtemp: IGraph.node -> Temp.temp,
				  moves: (Graph.node * Graph.node) list}

	      val interferenceGraph: 
		  Flow.flowgraph -> 
		  igraph * (Graph.node -> Temp.temp list)

	      (* val show: outstream * igraph -> unit*)

	      (*Maintain a data structure that remembers what is live at the exit of each flow-graph node*)
	      type liveSet
	      type liveMap

	  end  
  = struct
type liveSet = unit Temp.Table.table * Temp.temp list
type liveMap = liveSet Graph.Table.table


datatype igraph =
	 IGRAPH of {graph: IGraph.graph,
		    tnode: Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    moves: (Graph.node * Graph.node) list}



(* val show: outstream * igraph -> unit*)

(*Maintain a data structure that remembers what is live at the exit of each flow-graph node*)
		   




fun interferenceGraph (Flow.FGRAPH{control, def,use,ismove}) = 
    (*nodeoutsetlist is a tuple of node and outset for each node*)
    let  val nodelist= Graph.nodes(control)
	
	 fun getlivemap (theoutmap) =
	    (   
	     let 
		 fun foldfun(thenode,oldlivemap) = 
		     
		     let 
			 val outset = valOf(Setmap.look(theoutmap,thenode)) 
			 val templist = tempSet.listItems(outset)
			 val unittable = foldl (fn(temp,curtable)=>Temp.Table.enter(curtable,temp,())) Temp.Table.empty  templist
			 val liveset = (unittable ,templist)
			 	       
		     in
			 Graph.Table.enter(oldlivemap,thenode,liveset)
			 
	             end
	     in 
		 foldl (foldfun) Graph.Table.empty nodelist	
	     end
		
	   )
	 
	 fun enteremptysets(thesetmap) = foldl(fn(anode,themap)=>Setmap.enter(themap,anode,tempSet.empty)) thesetmap nodelist (*populate in and out maps with empty sets per node*)	
	 val refoutmap= ref (enteremptysets(Setmap.empty))
	 val refoutmap'= ref (enteremptysets(Setmap.empty))
	 val refinmap = ref (enteremptysets(Setmap.empty))
	 val refinmap' = ref (enteremptysets(Setmap.empty))	     
	     
	 fun finallivemaps(i) =
	      (
	     let 
		val ()= (refinmap':= !refinmap)
		val ()= (refoutmap':= !refoutmap)		
		fun newlivemaps() = 
			
		     let fun foldfun(anode,curunit) = 
			let 

	
				val newinset = tempSet.union(
                                                 tempSet.addList(
                                                     tempSet.empty,
                                                     valOf(Graph.Table.look(use,anode))
                                                  ),
                                                  tempSet.difference(
                                                      valOf(Setmap.look(!refoutmap,anode)),
                                                       tempSet.addList(
                                                          tempSet.empty,
                                                           valOf(Graph.Table.look(def,anode))
                                                       )
                                                   )
                                                 )
				val newoutset = foldl (
                                                       fn(thesucc,theoutset) => 
                                                          tempSet.union(theoutset,
                                                                        valOf(Setmap.look(!refinmap,thesucc))
                                                          )
                                                       ) 
                                                       (tempSet.empty) (Graph.succ(anode))
				

				val () =  (refinmap:=(Setmap.enter(!refinmap,anode, newinset)))
				(*val () = ErrorMsg.error 31 (String.concat ["inset size: ", Int.toString(tempSet.numItems(newinset)) ])*)
				(*val () = ErrorMsg.error 31 (String.concat ["succ size: ", Int.toString(List.length(Graph.succ(anode))) ])*)
				(*val () = ErrorMsg.error 31 (String.concat ["outset size: ", Int.toString(tempSet.numItems(newoutset)) ])*)
 				val () =  (refoutmap:=(Setmap.enter(!refoutmap,anode, newoutset)))
			in
				()				
			end
  				  
			val inout = foldr (foldfun) () nodelist  
		     in

			inout 
		     end
		     
		 val ()= newlivemaps()
		 val notfixedpoint = List.exists(fn(anode)=> not (tempSet.equal(valOf(Setmap.look(!refinmap,anode)),valOf(Setmap.look(!refinmap',anode)) ) andalso tempSet.equal( valOf(Setmap.look(!refoutmap,anode)),valOf(Setmap.look(!refoutmap',anode))))  )  nodelist
	     in
		 if (notfixedpoint orelse i=0) then  finallivemaps(i+1)   
		 else
		     ()
			
	     end
	     )	

	 val () = finallivemaps(0)
	  
	 val (fininmap,finoutmap) = (!refinmap,!refoutmap)
	  										
	 val livemap = getlivemap (finoutmap)
	
	 fun getlivetemps(anode)=  #2 (valOf(Graph.Table.look(livemap,anode)))
	 
	 val theigraph = IGraph.newGraph()


	 fun enternodetemp(temp, nodemap,tempmap) = 
		(case Nodemap.look(nodemap,temp) of
		SOME(X)=>	(nodemap,tempmap)
		|NONE =>	(let val mynode = IGraph.newNode(theigraph) in (Nodemap.enter(nodemap,temp,mynode),Tempmap.enter(tempmap,mynode,temp)) end))

	 
	(*we're running through each def and creating a node for it in the igraph, and also a node-temp mapping*)		    

	 val (nodemap',tempmap') = foldl (fn(anode,(curnm,curtm))=> foldl (fn(deftemp,(anm,atm))=>enternodetemp(deftemp,anm,atm)) (curnm,curtm) (valOf(Graph.Table.look(def,anode))) )   (Nodemap.empty,Tempmap.empty)     nodelist
	val (nodemap,tempmap) = foldl (fn(anode,(curnm,curtm))=> foldl (fn(liveouttemp',(anm,atm))=>enternodetemp(liveouttemp',anm,atm)) (curnm,curtm) (#2(valOf(Graph.Table.look(livemap,anode)))) )   (nodemap',tempmap')     nodelist

	 fun temptonode(thetemp) = valOf(Nodemap.look(nodemap,thetemp))

	 fun nodetotemp (thenode) = valOf(Tempmap.look(tempmap,thenode))

	 fun interfere(deftemp,livetemp) = IGraph.mk_edge {from = temptonode(deftemp), to = temptonode(livetemp)}

	 fun makeedge (anode,aunit) = foldl (fn(adeftemp,myunit)=> foldl (fn(livetemp,curunit)=> interfere(adeftemp,livetemp))       () (#2(valOf(Graph.Table.look(livemap,anode)) )) )          () (valOf(Graph.Table.look(def,anode))) 

		 val () = foldl (fn(anode,aunit)=>  ((valOf(Graph.Table.look(def,anode))); () )   )  () nodelist



	 val () = foldl (makeedge) () nodelist   (*makes edges in theigraph between every deftemp and every liveout temp where it's defined*)


	(*val () = foldl (fn(node,theunit)=> ( ErrorMsg.error 0 (String.concat["liveoutnum: node: " , Int.toString (#2 node) , " ", Int.toString(List.length(getlivetemps(node))) ] );foldl (fn(atemp,theunit)=> ErrorMsg.error 0 (" temp is: " ^ Int.toString(atemp) ) )  () (getlivetemps(node) ) ) )  () nodelist*)

	(*val () = foldl (fn(node,theunit)=> ( ErrorMsg.error 0 (String.concat["node: " , Int.toString(#2 node) ] );foldl (fn(node,theunit)=> ErrorMsg.error 2 (" succ is: " ^ Int.toString(#2 node) ) )  () (Graph.succ(node) ) ) )  () nodelist*)
	(*val () = foldl (fn(n,theunit)=>   (ErrorMsg.error 31 (String.concat ["succ size: ", (Int.toString(List.length(Graph.succ(n)))) ] ) )) () nodelist*)



    in 
		
	(IGRAPH{graph = theigraph, tnode= temptonode, gtemp=nodetotemp, moves = []} ,getlivetemps)

    end				
    
    

end



    (*
     fun show = 
(*For debugging purpose: print out a list of nodes in the interference graph*)


end
     *)



