structure FindEscape: sig val findEscape: Absyn.exp -> unit end =
struct
structure A = Absyn
type depth = int

type escEnv = (depth * bool ref) Symbol.table

	      
fun traverseVar(env:escEnv, d:depth, s:Absyn.var): unit = 
   

    case s of 
	A.SimpleVar(symbol,pos)=> 
	    let 
	
		val entryunit = (case(Symbol.look(env,symbol)) of
				     SOME((dp,theref)) =>  (if d > dp then theref:=true else ())
				   | NONE => ())
	    in 
		() 
	    end
	    
	  |A.FieldVar(var,symbol,pos)=>
	   
	   let val entryunit = (case(Symbol.look(env,symbol)) of
				    SOME((dp,theref)) => (if d > dp then theref:=true else ())
				  | NONE => ())
	   in 
	       traverseVar(env,d,var)
	   end
	  |A.SubscriptVar(var,exp,pos) => (traverseVar(env,d,var);traverseExp(env,d,exp))
						  
    
and traverseExp(env:escEnv, d:depth, s:Absyn.exp): unit =

	case s of
	A.ForExp{var,escape,lo,hi,body,pos}=> 
	    let
	
		val newenv = (escape:=false; Symbol.enter(env,var,(d,escape)))  			  
	    in 
		 traverseExp(newenv,d+1,body)
	    end
	  |A.VarExp v => traverseVar(env,d,v)
	  | A.LetExp{decs,body,pos} => traverseExp(traverseDecs(env,d,decs),d+1,body)
	  | A.SeqExp expposlist => 
	    let 
		val expunit= map (fn(exp,pos)=>(traverseExp(env,d,exp))) expposlist
	    in 
		()
	    end
	  |A.CallExp{func,args,pos} => 
	    let 
		val expunit=  (map (fn arg => traverseExp(env,d,arg)) args)

	    in 
		() 
	    end
	  | A.OpExp{left,oper,right,pos} =>
	    let 
		val unit1= traverseExp(env,d,left)
		val unit2= traverseExp(env,d,right)
	    in 
		() end
	  | A.RecordExp{fields,typ,pos} =>
	    let val expunit= map(fn(symbol,exp,pos)=>(traverseExp(env,d,exp))) fields
	    in
		() 
	    end
	  |A.AssignExp{var,exp,pos}=>(traverseVar(env,d,var);traverseExp(env,d,exp))
	  |A.IfExp{test,then',else',pos} =>
	    (case(else') of 
		 SOME(theelse) => (traverseExp(env,d,test);traverseExp(env,d,then');traverseExp(env,d,theelse))			
	       | NONE =>(traverseExp(env,d,test);traverseExp(env,d,then')))
	  | A.WhileExp{test,body,pos} => (traverseExp(env,d,test);traverseExp(env,d,body))
	  | A.BreakExp (pos)=>()
	  | A.ArrayExp{typ,size,init,pos}=>(traverseExp(env,d,size);traverseExp(env,d,init))
	  | A.NilExp =>()
	  | A.StringExp x=>()
	  | _ => ()		

		 
and traverseDecs(env, d, s: Absyn.dec list): escEnv = 
    let fun travdec(A.FunctionDec(fdlist),env)=
	    let fun foldfun({name,params,result,body,pos},theenv) =

		    let val theenv = foldl(fn({name,escape,typ,pos},myenv)=> (escape:=false; Symbol.enter(myenv,name,(d,escape)))) (theenv) (params)
		    in 
			(traverseExp(theenv,d+1,body) ;theenv) 
		    end

	    in 
		foldl (foldfun)(env)(fdlist)
	    end
	    
	  | travdec(A.VarDec{name,escape,typ,init,pos},env) = (escape:=false ; Symbol.enter(env,name,(d,escape)))										
	  | travdec(A.TypeDec({name,ty,pos}::xs),env)= env

	  | travdec(_,_) = env
			    
    in
	foldl(travdec)(env)(s)
    end
    
fun findEscape (prog: Absyn.exp) : unit =(traverseExp(Symbol.empty,0,prog))
					  
					  
end
