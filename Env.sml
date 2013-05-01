signature ENV =
sig
    type access   
    datatype enventry = 
	     VarEntry of {access: Translate.access, ty: Types.ty}
	   | FunEntry of {level: Translate.level, 
			  label: Temp.label, 
			  formals: Types.ty list, result: Types.ty}
			 
    val base_tenv : Types.ty Symbol.table 
    val base_venv: enventry Symbol.table 
end

structure Env :> ENV =
struct

structure T = Types
type access = unit

datatype enventry = 
	 VarEntry of {access: Translate.access, ty: Types.ty}
       | FunEntry of {level: Translate.level, 
		      label: Temp.label, 
		      formals: Types.ty list, result: Types.ty}

val base_tenv = let val T = Symbol.empty
		    val T1 = Symbol.enter(T,Symbol.symbol("int"),Types.INT)
                    val T2 = Symbol.enter(T1,Symbol.symbol("string"),Types.STRING)
		in
		    T2
		end

fun make_base_venv (name, args, result) =
    let
        val label = Temp.namedlabel(name)
        val level = Translate.newLevel{parent=Translate.outermost,
                                       name=label,
                                       formals=map (fn _ => false) args}
    in
        (Symbol.symbol(name), FunEntry{label=label,level=level,formals=args,result=result})
    end
    
val base_venv = 
    let
        val functions = [("print", [T.STRING], T.UNIT),
                         ("flush", [], T.UNIT),
                         ("getchar", [], T.STRING),
                         ("ord", [T.STRING], T.INT),
                         ("chr", [T.INT], T.STRING),
                         ("size", [T.STRING], T.INT),
                         ("substring", [T.STRING,T.INT,T.INT], T.STRING),
                         ("concat", [T.STRING,T.STRING], T.STRING),
                         ("not", [T.INT], T.INT),
                         ("exit", [T.INT], T.BOTTOM) ]
	val mapping = map make_base_venv functions
    	val empty = Symbol.empty
	fun foldFun ((symbol,entry),env) = Symbol.enter(env,symbol,entry)
    in
        foldr foldFun (empty) (mapping)
    end      
end
