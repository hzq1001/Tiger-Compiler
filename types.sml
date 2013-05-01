structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	  | NAME of Symbol.symbol * ty option ref
	  | UNIT
          | BOTTOM 
 
  fun isSameTy (ty1:ty,ty2:ty) = if ty1 = ty2 then true else false
  fun isInt (ty1:ty) = if ty1 = INT then true else false
  
  fun tyToStr(RECORD(_))= "RECORD"
      |tyToStr(NIL)="NIL"
      |tyToStr(INT)="INT"
      |tyToStr(STRING)="STRING"
      |tyToStr(ARRAY(_))="ARRAY"
      |tyToStr(NAME(_))="NAME"
      |tyToStr(UNIT)="UNIT" 
      |tyToStr(BOTTOM)="BOTTOM"   

fun printTy(x) = ( TextIO.output(TextIO.stdOut, tyToStr(x)); TextIO.output(TextIO.stdOut,"\n") )

  fun isSubType (BOTTOM,_) =  true
    | isSubType (NIL, RECORD(_)) =  true
    | isSubType (INT, INT) =  true
    | isSubType (STRING,STRING) =  true
    | isSubType (RECORD(x,y),RECORD(a,b)) =  (x = a) andalso (y = b) 
    | isSubType (ARRAY(x,y),ARRAY(a,b)) = (x = a) andalso (y = b) 
    | isSubType (UNIT,UNIT) =  true
    | isSubType (x,y) = (TextIO.output(TextIO.stdOut,tyToStr(x)); TextIO.output(TextIO.stdOut," not subtype of "); TextIO.output(TextIO.stdOut,tyToStr(y)); TextIO.output(TextIO.stdOut,"\n"); false)
			

end

