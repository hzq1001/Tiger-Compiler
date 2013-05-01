structure newSemant =
struct

structure A = Absyn
structure E = Env
structure Ty = Types
structure Tr = Translate
structure Er = ErrorMsg
exception Error

type venv = E.enventry Symbol.table
type tenv = Ty.ty Symbol.table
type expty = {exp: Tr.exp, ty: Ty.ty}


val tenv = E.base_tenv
val venv = E.base_venv

(*look up symbol in the type env*)
fun typeLookUp (tenv,symbol,pos) = 
    case Symbol.look(tenv,symbol) of
	SOME t => t
      | NONE => (Er.error pos("Type is not defined: " ^ Symbol.name(symbol));Ty.BOTTOM)


(*translate Absyn.ty to Types.ty*)
fun translateTy (tenv,t) =
    case t of 
	A.NameTy(symbol,pos) => typeLookUp(tenv,symbol,pos)
      | A.RecordTy(fieldList) => 
	let fun mapFun ({name,escape,typ,pos}) = 
		let
		    val t = typeLookUp(tenv,typ,pos)
		in
		    (name,t)
		end
	    (*check duplicate field in the field list*)
	    fun checkDup (fieldHead::fieldTail) =
		let
		    fun existFun ({name,escape,typ,pos}) =
			if(#name fieldHead) = name then
			    (Er.error pos ("Duplicate field: " ^ Symbol.name(name));true)
			else
			    false
		in
		    (List.exists existFun fieldTail;checkDup(fieldTail))
		end
	      | checkDup [] = ()
	in
	    (checkDup(fieldList);Ty.RECORD((map mapFun fieldList),ref ()))
	end

      | A.ArrayTy(symbol,pos) => 
	let val t = typeLookUp(tenv,symbol,pos)
	in
	    Ty.ARRAY(t,ref ())
	end

fun actual_ty (Ty.NAME(symbol,tyOpt)) = 
    (case !tyOpt of 
	 SOME t => actual_ty t
       | NONE => raise Error)
  | actual_ty t = t

fun indexOf(a, list) =
    let
	fun indexOfA(a,[],i) = ~1
	  | indexOfA(a,x::xs,i) =
	    if(a=x) then i else indexOfA(a,xs,i+1)
    in
	indexOfA(a,list,0)
    end


fun okBinOpType (A.PlusOp,Ty.INT) = true
  | okBinOpType (A.MinusOp,Ty.INT) = true
  | okBinOpType (A.TimesOp,Ty.INT) = true 
  | okBinOpType (A.DivideOp,Ty.INT) = true 
  | okBinOpType (A.LtOp,Ty.INT) = true
  | okBinOpType (A.LeOp,Ty.INT) = true
  | okBinOpType (A.GtOp,Ty.INT) = true 
  | okBinOpType (A.GeOp,Ty.INT) = true 
  | okBinOpType (A.LtOp,Ty.STRING) = true
  | okBinOpType (A.LeOp,Ty.STRING) = true
  | okBinOpType (A.GtOp,Ty.STRING) = true 
  | okBinOpType (A.GeOp,Ty.STRING) = true
  | okBinOpType (A.EqOp,Ty.INT) = true
  | okBinOpType (A.NeqOp,Ty.INT) = true
  | okBinOpType (A.EqOp,Ty.STRING) = true
  | okBinOpType (A.NeqOp,Ty.STRING) = true  
  | okBinOpType (A.EqOp,Ty.RECORD _) = true
  | okBinOpType (A.NeqOp,Ty.RECORD _) = true  
  | okBinOpType (A.EqOp,Ty.ARRAY _) = true
  | okBinOpType (A.NeqOp,Ty.ARRAY _) = true
  | okBinOpType (_,_) = false


fun transExp (venv,tenv,breakbool,clevel,break) =
    let fun trexp (A.VarExp v) = trvar v
	  | trexp (A.NilExp) = {exp = Tr.nilExp(), ty = Ty.NIL}
          | trexp (A.IntExp n) = {exp = Tr.intExp(n), ty = Ty.INT}
	  | trexp (A.StringExp (str, pos)) = {exp = Tr.stringExp(str), ty = Ty.STRING}

	  | trexp (A.CallExp{func, args, pos}) = 
	    let  val result = 
		     case Symbol.look(venv,func) of
			 SOME(E.FunEntry{level,label,formals,result}) => 
			 let
			     val argList = map trexp args
			     val argTyList = map (#ty) argList
			     val expList = map (#exp) argList
			     val ac_argTyList = map actual_ty argTyList
			     val ac_formals = map actual_ty formals
			 in
			     if (length formals <> length args) 
			     then (Er.error pos "argument number does not match";{exp = Tr.errorExp(), ty = Ty.BOTTOM})
			     else if(not (ListPair.all(Ty.isSubType) (ac_argTyList,ac_formals))) 
			     then (Er.error pos "argument type mismatch";{exp = Tr.errorExp(), ty = Ty.BOTTOM})
			     else {exp = Tr.callExp(level,clevel,func,expList), ty = actual_ty result}
			 end
		       | _ => (Er.error pos "Function not defined"; {exp =Tr.errorExp(),ty=Ty.BOTTOM})

	    in
		result
	    end

	  | trexp (A.OpExp{left, oper, right, pos}) = 
            let  val {ty = tyleft , exp = expleft } = trexp left
		 val {ty = tyright, exp = expright} = trexp right
	    in
		if(not (Ty.isSubType(tyright, tyleft))) 
		then (Er.error pos "BiOp type mismatch"; {exp =Tr.errorExp (),ty = Ty.BOTTOM})
		else if (not (okBinOpType(oper,tyleft))) 
		then (Er.error pos "Oper and type mismatch"; {exp =Tr.errorExp (),ty = Ty.BOTTOM})
		else {exp = Tr.opExp (expleft,oper,expright), ty = Ty.INT}
	    end
		
   (*TODO: Has some problem// can't see any problem; maybe it's now fixed*)
	  | trexp (A.SeqExp []) = {exp = Tr.seqExp [], ty = Ty.UNIT}
	  | trexp (A.SeqExp exps) = 
	    let 
		val trSeqExp = map (fn(e,pos)=>trexp e) exps	
	    in
		List.last(trSeqExp)
	    end

	  | trexp (A.AssignExp{var, exp, pos}) = 
	    let  val {ty = tyvar , exp = expvar} = trvar var
		 val {ty = tyexp , exp = expexp} = trexp exp
	    in
		if Ty.isSubType(tyexp,tyvar) then 
		    {exp = Tr.assignExp (expvar,expexp), ty = Ty.UNIT} 
		else 
		    ( Er.error pos "Type mismatch for ASSIGN";{exp = Tr.errorExp (), ty = Ty.BOTTOM})
	    end

	  | trexp (A.IfExp{test, then', else'=NONE, pos}) = 
            let val {ty = tytest, exp = exptest} = trexp test
		val {ty = tythen, exp = expthen } = trexp then'
	    in
		if (not (Ty.isSubType (tytest,Ty.INT))) then 
		    (Er.error pos "Wrong Type for IF";{exp = Tr.errorExp (), ty = Ty.BOTTOM})
		else if Ty.isSubType(tythen, Ty.UNIT) then
		    {exp = Tr.ifThenExp(exptest, expthen), ty = Ty.UNIT}
		else
		    (Er.error pos "Wrong Type for THEN";{exp = Tr.errorExp  (), ty = Ty.BOTTOM})
	    end

	  | trexp (A.IfExp{test, then', else'=SOME(else'), pos}) = 
            let val {ty = tytest, exp = exptest} = trexp test
		val {ty = tythen, exp = expthen } = trexp then'
		val {ty = tyelse, exp = expelse} = trexp else'
	    in
		if (not (Ty.isSubType(tytest,Ty.INT))) then 
		    (Er.error pos "Wrong Type for IF";{exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else if(not (Ty.isSubType(tyelse,tythen))) then
		    (Er.error pos "Type mismatch for THEN and ELSE";{exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else
		    {exp = Tr.ifThenElseExp(exptest,expthen,expelse), ty = tythen}
	    end

		 (*TODO: Need to deal with break; Dealt with break*)
	  | trexp (A.WhileExp{test, body, pos}) = 
	    let 
			val {ty = tytest, exp = exptest} = trexp test
			
			val breakLabel = Temp.newlabel()
			val {ty = tybody, exp = expbody} = transExp(venv,tenv,true,clevel,breakLabel) body

	    in
		if (not (Ty.isSubType(tytest,Ty.INT))) then 
		    (Er.error pos "Wrong Type for WHILE";{exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else if Ty.isSubType(tybody,Ty.UNIT) then
		    {exp=Tr.whileExp(exptest,expbody,breakLabel), ty=Ty.UNIT}
		else
		    (Er.error pos "Wrong Type for body"; {exp = Tr.errorExp(), ty = Ty.BOTTOM})
	    end
	(*Need to deal with escape; dealt with escape*)    
	  | trexp (A.ForExp{var, escape, lo, hi, body, pos}) =
	    let 
		val access = Tr.allocLocal (clevel)(!escape)
		val {ty = tylo, exp = explo} = trexp lo
		val {ty = tyhi, exp = exphi} = trexp hi
		val venv' = Symbol.enter (venv, var, E.VarEntry {access = access, ty=Types.INT})
		val breaklabel = Temp.newlabel()
		val {ty = tybody, exp = expbody} = transExp(venv',tenv,true,clevel,breaklabel) body
	    in
		if (not (Ty.isSubType(tylo, Ty.INT))) then 
		    (Er.error pos "Wrong tpe for lo"; {exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else if (not (Ty.isSubType(tyhi, Ty.INT))) then
		    (Er.error pos "Wrong tpe for hi"; {exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else if (not (Ty.isSubType(tybody, Ty.UNIT))) then
		    (Er.error pos "Wrong tpe for body"; {exp = Tr.errorExp(), ty = Ty.BOTTOM})
		else
		    {exp = Tr.forExp(Tr.simpleVar(access,clevel),explo,exphi,expbody,breaklabel), ty = Ty.UNIT}
	    end
	
	  | trexp (A.BreakExp pos) = if (not breakbool) then (Er.error pos "Not in a loop"; {exp = Tr.errorExp(), ty = Ty.BOTTOM}) else {exp = Tr.breakExp(break), ty = Ty.BOTTOM}

	  
	  | trexp (A.LetExp{decs, body, pos}) = 
	    let 
			val (venv', tenv',trdeclist) = foldl (fn (dec, (v, t,listsofar)) => 
					let val resultsofar = transDec(v, t,clevel) dec
					in
						(#1(resultsofar),#2(resultsofar),(listsofar)@(#3(resultsofar))) 
					end) 
				   (venv, tenv,[]) decs
				   
			val {exp = expbody,ty = tybody} = transExp(venv',tenv',false,clevel,break) body
	    in
			{exp = Tr.letExp(trdeclist,expbody),ty = tybody}
	    end

	  | trexp (A.RecordExp{fields, typ, pos}) =     
	    let
		val typ' = typeLookUp(tenv,typ,pos)
		val recordType = actual_ty typ'
		val theexplist:Tr.exp list ref = ref []
		
	    in
		case recordType of
		    Ty.RECORD(list,unique) => 
		    let 
			val sortFun = ListMergeSort.sort(fn(x,y) => String.> (Symbol.name(#1(x)), Symbol.name(#1(y))))
			val symbolTyList = sortFun(list)
			val extractField = map (fn(symbol,exp,pos) => (symbol, (let val thetr = trexp exp in (theexplist:=(#exp(thetr)::(!theexplist));#ty(thetr)) end))) fields
			val fieldList = sortFun(extractField) 
			val compareList = ListPair.zip(symbolTyList,fieldList) 
		    in
			if (List.length(fields) <> List.length(list)) then (Er.error pos "Record fields length mismatch";{exp =Tr.errorExp(), ty = Ty.BOTTOM})
			else if not
				    let fun mapFun ((s1:Symbol.symbol,ty1),(s2:Symbol.symbol,ty2))  = ((s1 = s2) andalso (Ty.isSubType(ty2,ty1)))
				    in
					List.exists mapFun compareList
				    end
			then (Er.error pos "Symbol not found or field type mismatch";{exp =Tr.errorExp(), ty = Ty.BOTTOM})

			else {exp =Tr.recordExp(fields,typ,!theexplist), ty = Ty.RECORD(list,unique)}
		    end

		  | _ => (Er.error pos "Record type not defined";{exp =Tr.errorExp(), ty = Ty.BOTTOM})
	    end
	  
	  | trexp (A.ArrayExp{typ, size, init, pos}) = 
	    let 
		val {exp=expsize, ty=tysize} = trexp size
		val {exp=expinit, ty=tyinit} = trexp init
		    
		val typ' = typeLookUp(tenv,typ,pos)
		val arrayType = actual_ty typ'
	    in
		case arrayType of
		    Ty.ARRAY(t,unique) => 
		    if (not (Ty.isSubType(tyinit,(actual_ty t)))) 
		    then (Er.error pos "Wrong init type for array";{exp=Tr.errorExp(), ty=Ty.BOTTOM})
		    else if (not (Ty.isSubType(tysize,Ty.INT))) 
		    then (Er.error pos "Wrong size type for array";{exp=Tr.errorExp(), ty=Ty.BOTTOM})
		    else {exp=Tr.arrayExp(typ,expsize,expinit),ty= Ty.ARRAY(actual_ty t,unique)}					
		  | _ => (Er.error pos "Array type not defined" ; {exp=Tr.errorExp(), ty=Ty.BOTTOM})

	    end


	and trvar (A.SimpleVar (symbol,pos)) = 
	    (case Symbol.look(venv,symbol) of 
		 SOME(E.VarEntry{access=access,ty=tyvar}) => {exp = Tr.simpleVar(access,clevel), ty = actual_ty tyvar}
	       | _ => (Er.error pos "Variable not defined" ;{exp = Tr.errorExp(), ty = Ty.BOTTOM}))
	    
	  | trvar (A.FieldVar(var,symbol,pos)) =  
	    let 
		val {exp = varexp,ty =varty} = trvar var
		fun findTy (((symbol',ty)::stList),symbol) = if symbol = symbol' then ty else findTy(stList,symbol)
		  | findTy ([],symbol) = Ty.BOTTOM
	    
		val fieldempty = 
		    case varty of 
			Ty.RECORD(symbolTyList,unique) => 
			let
			    val fieldName = (map #1 symbolTyList)
			    val index = indexOf(symbol,fieldName)
			in 
			    if index <> ~1
			    then {exp=Tr.fieldVar(varexp,index), ty = findTy(symbolTyList,symbol)}
			    else (Er.error pos "Field variable not in Record"; {exp=Tr.errorExp(), ty = Ty.BOTTOM})
			end
		      | _ => (Er.error pos "Lvalue in Fieldvar is not a Record" ; {exp=Tr.errorExp(), ty = Ty.BOTTOM})
	    in 
		fieldempty
	    end
	  | trvar (A.SubscriptVar (var, exp, pos)) = 
	    let 
		val {exp=varexp,ty=varty} = trvar var
		val vartype = actual_ty varty
		val {exp=subexp,ty=subty} = trexp exp
		val arrayempty =  
		    case vartype of
			Ty.ARRAY(theTy,unique)=> if subty = Ty.INT 
						 then {exp=Tr.subscriptVar(varexp,subexp), ty = theTy} 
						 else (Er.error pos "Array index not int"; {exp=Tr.errorExp(),ty=Ty.BOTTOM})
		      | _ => (Er.error pos "Indexing requires an array" ; {exp=Tr.errorExp(),ty=Ty.BOTTOM})
	    in
		arrayempty
	    end

    in
	trexp
    end

and transDec(venv,tenv,clevel) = 
    let fun trdec (A.FunctionDec fundecs) = 

	    let 
		fun checkDup (fundecHead::fundecTail) =
		    let
			fun existFun ({name,params,result,body,pos}) =
			    if(#name fundecHead) = name then
				(Er.error pos ("Duplicate fundec: " ^ Symbol.name(name));true)
			    else
				false
		    in
			(List.exists existFun fundecTail;checkDup(fundecTail))
		    end
		  | checkDup [] = ()

		val checkDup' = checkDup fundecs

		fun enterHeader ({name,params,result,body,pos}, env) =
		    let   
			val retTy = case result of
					SOME(rname,rpos) => typeLookUp(tenv,rname,rpos)
				      | NONE => Ty.UNIT
			val params' = (map (fn({name,escape,typ,pos}) => {name = name, ty = typeLookUp(tenv,typ,pos)}) params)
			val theformals = map (fn(theboolref)=> (!(#escape(theboolref)))) params
			val newlevel = Tr.newLevel({parent=clevel,name=name,formals=theformals})
		    in
			    Symbol.enter(env,name,E.FunEntry{level=newlevel,label=name,formals = (map #ty params') ,result = retTy})
		    end

		val venv' = foldl enterHeader venv fundecs

		fun processBody ({name,params,result,body,pos},(venv,tenv)) = 
		    let 
			fun updt ({name,escape,typ,pos},(venv,tenv)) =
			    let
				val t = typeLookUp(tenv,typ,pos)
				val access= Tr.allocLocal(clevel)(!escape)
			    in
				(Symbol.enter(venv,name,E.VarEntry{access=access,ty = t}),tenv)
			    end
			
			val (venv',tenv') = foldl updt (venv,tenv) params
		
			val retTy = case result of
					SOME(rname,rpos) => actual_ty (typeLookUp(tenv,rname,rpos))
				      | NONE => Ty.UNIT
		
			val {exp = expbody, ty = tybody} = transExp(venv',tenv',false,clevel,Temp.newlabel()) body
			val thelevel = case Symbol.look(venv,name) of
				SOME(E.FunEntry{level,label,formals ,result}) => level
			      | _ => (Er.error pos "Function not in environment"; clevel)
				
			val someunit= Tr.procEntryExit(thelevel,expbody);
			
		    in
			if retTy <> tybody then (Er.error pos "Function return type does not match";(venv,tenv))
			else (venv,tenv')
		    end	    

	    in
		 (foldl processBody (venv',tenv) fundecs;(venv',tenv,[]))
	    end

	  | trdec (A.VarDec{name, escape, typ = NONE, init, pos}) = 
	    let 
		val {exp = expinit, ty = tyinit} = transExp(venv,tenv,false,clevel,Temp.newlabel()) init	
		val access = Tr.allocLocal (clevel)(!escape)
		val venv' = case tyinit of 
				Ty.NIL => (Er.error pos "Initializing nil expressions not constrained by record type";venv)
			      | _ => Symbol.enter(venv,name,E.VarEntry{access=access,ty = tyinit})
		val assignval = Tr.assignExp(Tr.simpleVar(access,clevel),expinit)
	
	    in
		(venv',tenv,[assignval])
	    end
	  | trdec (A.VarDec{name, escape, typ = SOME(typ',typpos), init, pos}) = 
	    let val {exp = expinit, ty = tyinit} = transExp(venv,tenv,false,clevel,Temp.newlabel()) init
		val access = Tr.allocLocal (clevel) (!escape)
		val assignval = Tr.assignExp(Tr.simpleVar(access,clevel),expinit)
		val newenv =
	            case Symbol.look(tenv,typ') of
			SOME t => if Ty.isSubType(tyinit,actual_ty t) then (Symbol.enter(venv,name,E.VarEntry{access = access, ty=t}),tenv,[assignval]) 
                                  else (Er.error pos "Type Mismatch for Vardec"; (venv,tenv, []))
		      | NONE => (Er.error pos "Type is not defined"; (venv,tenv, []))
		
	    in
		newenv
	    end 

	  | trdec (A.TypeDec tys) = 
	    let
		val names = map #name tys
		val types = map #ty tys

		fun checkDup (tydecHead::tydecTail) =
		    let
			fun existFun ({name,ty,pos}) =
			    if(#name tydecHead) = name then
				(Er.error pos ("Duplicate tydec: " ^ Symbol.name(name));true)
			    else
				false
		    in
			(List.exists existFun tydecTail;checkDup(tydecTail))
		    end
		  | checkDup [] = ()

		val checkDup' = checkDup tys
		fun enterHeader ({name,ty,pos},env) = Symbol.enter(env,name,Types.NAME(name,ref NONE))
		val tenv' = foldl enterHeader tenv tys
		val nameTypes = map (fn t=> translateTy(tenv',t)) types
		fun updateTy (name,nameType) =
		    let val(SOME (Types.NAME(n,r))) = Symbol.look(tenv',name)
		    in 
			r := SOME nameType
		    end
		val updateTys = app updateTy (ListPair.zip(names,nameTypes))
	    in
		(venv,tenv',[])
	    end
    in
	trdec
    end

fun transProg prog =
    let
	val venv = E.base_venv
	val tenv = E.base_tenv
	val firstlevel = Tr.newLevel {
			     name=Temp.namedlabel "tig_main",
			     parent=Tr.outermost,
			     formals=[]}
	val break = Temp.newlabel()

	val {exp, ty} = transExp(venv, tenv, false, firstlevel, break) (prog)
    in
	(*{exp=exp,ty=ty}*)
	(Translate.procEntryExit(firstlevel,exp); Translate.getResult())
    end

end

