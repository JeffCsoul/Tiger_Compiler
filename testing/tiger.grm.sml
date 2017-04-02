
functor TigerLrValsFun(structure Token : TOKEN
                                structure A: ABSYN
                                structure Symbol: SYMBOL
                                sharing type A.symbol=Symbol.symbol) = 
struct
structure ParserData=
struct
structure Header = 
struct
type tydec = {name: A.symbol, ty: A.ty, pos: A.pos}


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\000\000\000\000\
\\001\000\001\000\174\000\005\000\174\000\007\000\174\000\009\000\174\000\
\\011\000\174\000\013\000\174\000\015\000\174\000\016\000\174\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\031\000\174\000\032\000\174\000\035\000\174\000\036\000\174\000\
\\038\000\174\000\039\000\174\000\043\000\174\000\044\000\174\000\
\\045\000\174\000\000\000\
\\001\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\009\000\047\000\024\000\011\000\030\000\010\000\033\000\009\000\
\\034\000\008\000\037\000\007\000\041\000\006\000\042\000\005\000\000\000\
\\001\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\024\000\011\000\030\000\010\000\033\000\009\000\034\000\008\000\
\\037\000\007\000\039\000\090\000\041\000\006\000\042\000\005\000\000\000\
\\001\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\024\000\011\000\030\000\010\000\033\000\009\000\034\000\008\000\
\\037\000\007\000\041\000\006\000\042\000\005\000\000\000\
\\001\000\002\000\041\000\000\000\
\\001\000\002\000\069\000\000\000\
\\001\000\002\000\070\000\000\000\
\\001\000\002\000\071\000\000\000\
\\001\000\002\000\078\000\000\000\
\\001\000\002\000\113\000\012\000\112\000\029\000\111\000\000\000\
\\001\000\002\000\115\000\000\000\
\\001\000\002\000\139\000\000\000\
\\001\000\002\000\144\000\000\000\
\\001\000\002\000\146\000\000\000\
\\001\000\002\000\148\000\000\000\
\\001\000\002\000\154\000\000\000\
\\001\000\002\000\159\000\000\000\
\\001\000\006\000\093\000\028\000\092\000\000\000\
\\001\000\006\000\130\000\000\000\
\\001\000\006\000\143\000\017\000\142\000\000\000\
\\001\000\006\000\157\000\000\000\
\\001\000\007\000\077\000\009\000\076\000\015\000\031\000\016\000\030\000\
\\017\000\029\000\018\000\028\000\019\000\027\000\020\000\026\000\
\\021\000\025\000\022\000\024\000\023\000\023\000\024\000\022\000\
\\025\000\021\000\026\000\020\000\000\000\
\\001\000\007\000\077\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\039\000\109\000\000\000\
\\001\000\008\000\094\000\000\000\
\\001\000\009\000\075\000\000\000\
\\001\000\009\000\105\000\000\000\
\\001\000\009\000\129\000\000\000\
\\001\000\011\000\104\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\000\000\
\\001\000\011\000\134\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\000\000\
\\001\000\013\000\102\000\000\000\
\\001\000\013\000\140\000\000\000\
\\001\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\031\000\074\000\000\000\
\\001\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\035\000\118\000\000\000\
\\001\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\036\000\073\000\000\000\
\\001\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\036\000\145\000\000\000\
\\001\000\017\000\091\000\000\000\
\\001\000\017\000\103\000\000\000\
\\001\000\017\000\152\000\000\000\
\\001\000\017\000\153\000\000\000\
\\001\000\028\000\072\000\000\000\
\\001\000\028\000\128\000\000\000\
\\001\000\038\000\068\000\000\000\
\\001\000\039\000\108\000\000\000\
\\001\000\040\000\126\000\000\000\
\\162\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\163\000\028\000\016\000\000\000\
\\164\000\000\000\
\\165\000\000\000\
\\166\000\000\000\
\\167\000\000\000\
\\168\000\000\000\
\\169\000\000\000\
\\170\000\000\000\
\\171\000\000\000\
\\172\000\000\000\
\\173\000\025\000\021\000\026\000\020\000\000\000\
\\175\000\017\000\029\000\018\000\028\000\019\000\027\000\020\000\026\000\
\\021\000\025\000\022\000\024\000\023\000\023\000\024\000\022\000\
\\025\000\021\000\026\000\020\000\000\000\
\\176\000\016\000\030\000\017\000\029\000\018\000\028\000\019\000\027\000\
\\020\000\026\000\021\000\025\000\022\000\024\000\023\000\023\000\
\\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\177\000\000\000\
\\178\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\179\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\180\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\181\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\
\\032\000\119\000\000\000\
\\182\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\183\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\184\000\000\000\
\\185\000\000\000\
\\186\000\000\000\
\\187\000\000\000\
\\188\000\000\000\
\\189\000\008\000\052\000\010\000\051\000\012\000\050\000\014\000\049\000\000\000\
\\189\000\010\000\101\000\014\000\049\000\000\000\
\\189\000\010\000\101\000\014\000\049\000\040\000\124\000\000\000\
\\190\000\000\000\
\\191\000\000\000\
\\192\000\000\000\
\\193\000\007\000\120\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\000\000\
\\194\000\000\000\
\\195\000\000\000\
\\196\000\002\000\015\000\003\000\014\000\004\000\013\000\008\000\012\000\
\\024\000\011\000\030\000\010\000\033\000\009\000\034\000\008\000\
\\037\000\007\000\041\000\006\000\042\000\005\000\000\000\
\\197\000\000\000\
\\198\000\005\000\107\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\000\000\
\\199\000\000\000\
\\200\000\002\000\080\000\000\000\
\\201\000\000\000\
\\202\000\005\000\136\000\015\000\031\000\016\000\030\000\017\000\029\000\
\\018\000\028\000\019\000\027\000\020\000\026\000\021\000\025\000\
\\022\000\024\000\023\000\023\000\024\000\022\000\025\000\021\000\
\\026\000\020\000\000\000\
\\203\000\000\000\
\\204\000\000\000\
\\205\000\000\000\
\\206\000\000\000\
\\207\000\000\000\
\\208\000\000\000\
\\209\000\000\000\
\\210\000\000\000\
\\211\000\000\000\
\\212\000\000\000\
\\213\000\043\000\040\000\044\000\039\000\045\000\038\000\000\000\
\\214\000\000\000\
\\215\000\000\000\
\\216\000\000\000\
\\217\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\218\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\219\000\045\000\038\000\000\000\
\\220\000\000\000\
\\221\000\000\000\
\\222\000\000\000\
\\223\000\000\000\
\\224\000\000\000\
\\225\000\000\000\
\\226\000\002\000\117\000\000\000\
\\227\000\000\000\
\\228\000\005\000\150\000\000\000\
\\229\000\043\000\040\000\044\000\039\000\000\000\
\\230\000\000\000\
\\231\000\000\000\
\\232\000\043\000\040\000\000\000\
\\233\000\000\000\
\\234\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\235\000\015\000\031\000\016\000\030\000\017\000\029\000\018\000\028\000\
\\019\000\027\000\020\000\026\000\021\000\025\000\022\000\024\000\
\\023\000\023\000\024\000\022\000\025\000\021\000\026\000\020\000\000\000\
\\236\000\044\000\039\000\045\000\038\000\000\000\
\\237\000\000\000\
\\238\000\000\000\
\"
val actionRowNumbers =
"\004\000\046\000\045\000\047\000\
\\066\000\097\000\005\000\004\000\
\\004\000\004\000\002\000\052\000\
\\051\000\071\000\004\000\004\000\
\\004\000\004\000\088\000\087\000\
\\090\000\089\000\096\000\095\000\
\\094\000\093\000\092\000\091\000\
\\004\000\004\000\116\000\120\000\
\\097\000\103\000\113\000\042\000\
\\006\000\007\000\008\000\040\000\
\\034\000\032\000\054\000\025\000\
\\022\000\049\000\070\000\009\000\
\\084\000\004\000\080\000\061\000\
\\001\000\056\000\055\000\057\000\
\\058\000\117\000\100\000\097\000\
\\113\000\098\000\104\000\120\000\
\\097\000\099\000\003\000\036\000\
\\018\000\024\000\004\000\004\000\
\\004\000\048\000\050\000\004\000\
\\072\000\030\000\037\000\028\000\
\\026\000\082\000\121\000\122\000\
\\115\000\114\000\043\000\023\000\
\\068\000\010\000\004\000\011\000\
\\110\000\033\000\064\000\063\000\
\\076\000\077\000\074\000\004\000\
\\059\000\004\000\073\000\053\000\
\\079\000\004\000\069\000\067\000\
\\105\000\044\000\110\000\106\000\
\\101\000\041\000\027\000\019\000\
\\004\000\004\000\004\000\029\000\
\\086\000\075\000\004\000\082\000\
\\012\000\031\000\004\000\020\000\
\\013\000\035\000\062\000\078\000\
\\072\000\083\000\014\000\060\000\
\\081\000\108\000\107\000\102\000\
\\004\000\015\000\112\000\004\000\
\\038\000\118\000\039\000\109\000\
\\016\000\065\000\004\000\004\000\
\\021\000\086\000\119\000\017\000\
\\085\000\112\000\111\000\000\000"
val gotoT =
"\
\\001\000\159\000\002\000\002\000\003\000\001\000\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\014\000\035\000\015\000\034\000\016\000\033\000\021\000\032\000\
\\022\000\031\000\023\000\030\000\000\000\
\\000\000\
\\002\000\040\000\003\000\001\000\000\000\
\\002\000\041\000\003\000\001\000\000\000\
\\002\000\042\000\003\000\001\000\000\000\
\\002\000\044\000\003\000\001\000\005\000\043\000\000\000\
\\000\000\
\\000\000\
\\004\000\046\000\000\000\
\\002\000\051\000\003\000\001\000\000\000\
\\002\000\052\000\003\000\001\000\000\000\
\\002\000\053\000\003\000\001\000\000\000\
\\002\000\054\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\055\000\003\000\001\000\000\000\
\\002\000\056\000\003\000\001\000\000\000\
\\022\000\057\000\023\000\030\000\000\000\
\\015\000\060\000\016\000\033\000\021\000\059\000\024\000\058\000\000\000\
\\014\000\061\000\015\000\034\000\016\000\033\000\021\000\032\000\
\\022\000\031\000\023\000\030\000\000\000\
\\015\000\062\000\016\000\033\000\000\000\
\\017\000\065\000\021\000\064\000\022\000\063\000\023\000\030\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\009\000\077\000\000\000\
\\002\000\079\000\003\000\001\000\000\000\
\\002\000\081\000\003\000\001\000\007\000\080\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\014\000\082\000\015\000\034\000\016\000\033\000\021\000\032\000\
\\022\000\031\000\023\000\030\000\000\000\
\\017\000\083\000\021\000\064\000\022\000\063\000\023\000\030\000\000\000\
\\000\000\
\\000\000\
\\015\000\060\000\016\000\033\000\021\000\059\000\024\000\084\000\000\000\
\\014\000\085\000\015\000\034\000\016\000\033\000\021\000\032\000\
\\022\000\031\000\023\000\030\000\000\000\
\\000\000\
\\002\000\087\000\003\000\001\000\005\000\086\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\093\000\003\000\001\000\000\000\
\\002\000\094\000\003\000\001\000\000\000\
\\002\000\095\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\002\000\097\000\003\000\001\000\006\000\096\000\000\000\
\\004\000\098\000\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\008\000\104\000\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\018\000\108\000\000\000\
\\002\000\112\000\003\000\001\000\000\000\
\\000\000\
\\019\000\114\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\002\000\119\000\003\000\001\000\000\000\
\\000\000\
\\002\000\120\000\003\000\001\000\000\000\
\\004\000\121\000\000\000\
\\000\000\
\\000\000\
\\002\000\123\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\019\000\125\000\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\002\000\129\000\003\000\001\000\000\000\
\\002\000\130\000\003\000\001\000\000\000\
\\002\000\097\000\003\000\001\000\006\000\131\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\010\000\133\000\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\002\000\135\000\003\000\001\000\000\000\
\\008\000\136\000\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\002\000\139\000\003\000\001\000\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\004\000\121\000\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\002\000\145\000\003\000\001\000\000\000\
\\000\000\
\\020\000\147\000\000\000\
\\002\000\149\000\003\000\001\000\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\002\000\153\000\003\000\001\000\000\000\
\\002\000\154\000\003\000\001\000\000\000\
\\000\000\
\\010\000\156\000\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\011\000\017\000\012\000\016\000\013\000\015\000\000\000\
\\000\000\
\\000\000\
\\020\000\158\000\000\000\
\\000\000\
\\000\000\
\"
val numstates = 160
val numrules = 77
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | STRING of unit ->  (string) | INT of unit ->  (int)
 | ID of unit ->  (string)
 | followfundecs of unit ->  ( ( A.dec list ) )
 | fundec of unit ->  (A.fundec)
 | fundecs of unit ->  ( ( A.fundec list ) )
 | vardec of unit ->  (A.dec)
 | fieldsplus of unit ->  ( ( A.field list ) )
 | fields of unit ->  ( ( A.field list ) ) | ty of unit ->  (A.ty)
 | followtydecs of unit ->  ( ( A.dec list ) )
 | tydec of unit ->  (tydec) | tydecs of unit ->  ( ( tydec list ) )
 | decs of unit ->  ( ( A.dec list ) ) | compop of unit ->  (A.oper)
 | addop of unit ->  (A.oper) | multop of unit ->  (A.oper)
 | recinitsplus of unit ->  ( ( (A.symbol * A.exp * pos) list ) )
 | recinits of unit ->  ( ( (A.symbol * A.exp * pos) list ) )
 | argsplus of unit ->  ( ( A.exp list ) )
 | funargs of unit ->  ( ( A.exp list ) )
 | exps of unit ->  ( ( (A.exp * pos) list ) )
 | expseq of unit ->  ( ( (A.exp * pos) list ) )
 | lvaluerest of unit ->  ( ( A.var -> A.var ) )
 | lvalue of unit ->  (A.var) | exp of unit ->  (A.exp)
 | program of unit ->  (A.exp)
end
type svalue = MlyValue.svalue
type result = A.exp
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn (T 32) => true | (T 33) => true | (T 34) => true | (T 40) => true
 | (T 36) => true | (T 37) => true | (T 38) => true | (T 42) => true
 | (T 43) => true | (T 44) => true | (T 28) => true | (T 29) => true
 | (T 30) => true | (T 31) => true | (T 35) => true | (T 39) => true
 | (T 41) => true | _ => false
val preferred_change : (term list * term list) list = 
(nil
,nil
 $$ (T 30))::
(nil
,nil
 $$ (T 31))::
(nil
,nil
 $$ (T 7))::
nil
val noShift = 
fn (T 0) => true | _ => false
val showTerminal =
fn (T 0) => "EOF"
  | (T 1) => "ID"
  | (T 2) => "INT"
  | (T 3) => "STRING"
  | (T 4) => "COMMA"
  | (T 5) => "COLON"
  | (T 6) => "SEMICOLON"
  | (T 7) => "LPAREN"
  | (T 8) => "RPAREN"
  | (T 9) => "LBRACK"
  | (T 10) => "RBRACK"
  | (T 11) => "LBRACE"
  | (T 12) => "RBRACE"
  | (T 13) => "DOT"
  | (T 14) => "OR"
  | (T 15) => "AND"
  | (T 16) => "EQ"
  | (T 17) => "NEQ"
  | (T 18) => "LT"
  | (T 19) => "LE"
  | (T 20) => "GT"
  | (T 21) => "GE"
  | (T 22) => "PLUS"
  | (T 23) => "MINUS"
  | (T 24) => "TIMES"
  | (T 25) => "DIVIDE"
  | (T 26) => "UMINUS"
  | (T 27) => "ASSIGN"
  | (T 28) => "ARRAY"
  | (T 29) => "IF"
  | (T 30) => "THEN"
  | (T 31) => "ELSE"
  | (T 32) => "WHILE"
  | (T 33) => "FOR"
  | (T 34) => "TO"
  | (T 35) => "DO"
  | (T 36) => "LET"
  | (T 37) => "IN"
  | (T 38) => "END"
  | (T 39) => "OF"
  | (T 40) => "BREAK"
  | (T 41) => "NIL"
  | (T 42) => "FUNCTION"
  | (T 43) => "VAR"
  | (T 44) => "TYPE"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn (T 1) => MlyValue.ID(fn () => ("bogus")) | 
(T 2) => MlyValue.INT(fn () => (1)) | 
(T 3) => MlyValue.STRING(fn () => ("")) | 
_ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 44) $$ (T 43) $$ (T 42) $$ (T 41) $$ (T 40) $$ (T 39) $$ (T 38)
 $$ (T 37) $$ (T 36) $$ (T 35) $$ (T 34) $$ (T 33) $$ (T 32) $$ (T 31)
 $$ (T 30) $$ (T 29) $$ (T 28) $$ (T 27) $$ (T 26) $$ (T 25) $$ (T 24)
 $$ (T 23) $$ (T 22) $$ (T 21) $$ (T 20) $$ (T 19) $$ (T 18) $$ (T 17)
 $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10)
 $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 0)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.exp exp1, exp1left, exp1right)) :: rest671)
) => let val  result = MlyValue.program (fn _ => let val  (exp as exp1
) = exp1 ()
 in (exp)
end)
 in ( LrTable.NT 0, ( result, exp1left, exp1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.lvalue lvalue1, lvalue1left, lvalue1right))
 :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  (
lvalue as lvalue1) = lvalue1 ()
 in (A.VarExp lvalue)
end)
 in ( LrTable.NT 1, ( result, lvalue1left, lvalue1right), rest671)
end
|  ( 2, ( ( _, ( _, NIL1left, NIL1right)) :: rest671)) => let val  
result = MlyValue.exp (fn _ => (A.NilExp))
 in ( LrTable.NT 1, ( result, NIL1left, NIL1right), rest671)
end
|  ( 3, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.expseq 
expseq1, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val 
 result = MlyValue.exp (fn _ => let val  (expseq as expseq1) = expseq1
 ()
 in (A.SeqExp expseq)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 4, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( _, LPAREN1left, _)) ::
 rest671)) => let val  result = MlyValue.exp (fn _ => (A.SeqExp nil))
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 5, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.exp exp1, _,
 _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (exp as exp1) = exp1 ()
 in (exp)
end)
 in ( LrTable.NT 1, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.INT INT1, INT1left, INT1right)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  (INT as INT1) = 
INT1 ()
 in (A.IntExp INT)
end)
 in ( LrTable.NT 1, ( result, INT1left, INT1right), rest671)
end
|  ( 7, ( ( _, ( MlyValue.STRING STRING1, (STRINGleft as STRING1left),
 STRING1right)) :: rest671)) => let val  result = MlyValue.exp (fn _
 => let val  (STRING as STRING1) = STRING1 ()
 in (A.StringExp (STRING,STRINGleft))
end)
 in ( LrTable.NT 1, ( result, STRING1left, STRING1right), rest671)
end
|  ( 8, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.funargs 
funargs1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, (IDleft as ID1left),
 _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let val 
 (ID as ID1) = ID1 ()
 val  (funargs as funargs1) = funargs1 ()
 in (
A.CallExp {func = (Symbol.symbol ID),
                                    args = funargs, pos = IDleft}
)
end)
 in ( LrTable.NT 1, ( result, ID1left, RPAREN1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: ( _, ( _, (
MINUSleft as MINUS1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (exp as exp1) = exp1 ()
 in (
A.OpExp {left = A.IntExp 0, oper = A.MinusOp,
                                  right = exp, pos = MINUSleft}
)
end)
 in ( LrTable.NT 1, ( result, MINUS1left, exp1right), rest671)
end
|  ( 10, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( 
MlyValue.multop multop1, _, _)) :: ( _, ( MlyValue.exp exp1, exp1left,
 _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  
exp1 = exp1 ()
 val  (multop as multop1) = multop1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp {left = exp1, oper = multop,
                                  right = exp2, pos = exp1left}
)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp2right), rest671)
end
|  ( 11, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( 
MlyValue.addop addop1, _, _)) :: ( _, ( MlyValue.exp exp1, exp1left, _
)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  
exp1 = exp1 ()
 val  (addop as addop1) = addop1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp {left = exp1, oper = addop,
                                  right = exp2, pos = exp1left}
)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp2right), rest671)
end
|  ( 12, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: ( _, ( 
MlyValue.compop compop1, _, _)) :: ( _, ( MlyValue.exp exp1, exp1left,
 _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  
exp1 = exp1 ()
 val  (compop as compop1) = compop1 ()
 val  exp2 = exp2 ()
 in (
A.OpExp {left = exp1, oper = compop,
                                  right = exp2, pos = exp1left}
)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp2right), rest671)
end
|  ( 13, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, exp1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp {test = exp1, then' = exp2,
                                  else'= SOME (A.IntExp 0), pos = exp1left}
)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp2right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, exp1left, _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp {test = exp1, then' = (A.IntExp 1),
                                  else' = (SOME exp2), pos = exp1left}
)
end)
 in ( LrTable.NT 1, ( result, exp1left, exp2right), rest671)
end
|  ( 15, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.recinits 
recinits1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, (IDleft as ID1left),
 _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let val 
 (ID as ID1) = ID1 ()
 val  (recinits as recinits1) = recinits1 ()
 in (
A.RecordExp {fields = recinits, 
                                      typ = (Symbol.symbol ID), 
                                      pos = IDleft}
)
end)
 in ( LrTable.NT 1, ( result, ID1left, RBRACE1right), rest671)
end
|  ( 16, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: _ :: ( _, 
( MlyValue.exp exp1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, (IDleft
 as ID1left), _)) :: rest671)) => let val  result = MlyValue.exp (fn _
 => let val  (ID as ID1) = ID1 ()
 val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.ArrayExp {typ = (Symbol.symbol ID),
                                     size = exp1, init = exp2, pos = IDleft}
)
end)
 in ( LrTable.NT 1, ( result, ID1left, exp2right), rest671)
end
|  ( 17, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.lvalue lvalue1, (lvalueleft as lvalue1left), _)) :: rest671))
 => let val  result = MlyValue.exp (fn _ => let val  (lvalue as 
lvalue1) = lvalue1 ()
 val  (exp as exp1) = exp1 ()
 in (
A.AssignExp {var = lvalue, exp = exp, 
                                      pos = lvalueleft}
)
end)
 in ( LrTable.NT 1, ( result, lvalue1left, exp1right), rest671)
end
|  ( 18, ( ( _, ( MlyValue.exp exp3, _, exp3right)) :: _ :: ( _, ( 
MlyValue.exp exp2, _, _)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) :: 
( _, ( _, (IFleft as IF1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 val  exp3 = exp3 ()
 in (
A.IfExp {test = exp1, then' = exp2, 
                                  else' = (SOME exp3), pos = IFleft}
)
end)
 in ( LrTable.NT 1, ( result, IF1left, exp3right), rest671)
end
|  ( 19, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, _, _)) :: ( _, ( _, (IFleft as IF1left), _)) :: 
rest671)) => let val  result = MlyValue.exp (fn _ => let val  exp1 = 
exp1 ()
 val  exp2 = exp2 ()
 in (
A.IfExp {test = exp1, then' = exp2, 
                                  else' = NONE, pos = IFleft}
)
end)
 in ( LrTable.NT 1, ( result, IF1left, exp2right), rest671)
end
|  ( 20, ( ( _, ( MlyValue.exp exp2, _, exp2right)) :: _ :: ( _, ( 
MlyValue.exp exp1, _, _)) :: ( _, ( _, (WHILEleft as WHILE1left), _))
 :: rest671)) => let val  result = MlyValue.exp (fn _ => let val  exp1
 = exp1 ()
 val  exp2 = exp2 ()
 in (
A.WhileExp {test = exp1, body = exp2, 
                                     pos = WHILEleft}
)
end)
 in ( LrTable.NT 1, ( result, WHILE1left, exp2right), rest671)
end
|  ( 21, ( ( _, ( MlyValue.exp exp3, _, exp3right)) :: _ :: ( _, ( 
MlyValue.exp exp2, _, _)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) ::
 _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, (FORleft as FOR1left
), _)) :: rest671)) => let val  result = MlyValue.exp (fn _ => let
 val  (ID as ID1) = ID1 ()
 val  exp1 = exp1 ()
 val  exp2 = exp2 ()
 val  exp3 = exp3 ()
 in (
A.ForExp {var = (Symbol.symbol ID), 
                                   escape = (ref true),
                                   lo = exp1, hi = exp2, body = exp3, 
                                   pos = FORleft}
)
end)
 in ( LrTable.NT 1, ( result, FOR1left, exp3right), rest671)
end
|  ( 22, ( ( _, ( _, (BREAKleft as BREAK1left), BREAK1right)) :: 
rest671)) => let val  result = MlyValue.exp (fn _ => (
A.BreakExp BREAKleft))
 in ( LrTable.NT 1, ( result, BREAK1left, BREAK1right), rest671)
end
|  ( 23, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.exp exp1, _, _)
) :: _ :: ( _, ( MlyValue.decs decs1, _, _)) :: ( _, ( _, (LETleft as 
LET1left), _)) :: rest671)) => let val  result = MlyValue.exp (fn _ =>
 let val  (decs as decs1) = decs1 ()
 val  (exp as exp1) = exp1 ()
 in (A.LetExp {decs = decs, body = exp, pos = LETleft})
end)
 in ( LrTable.NT 1, ( result, LET1left, END1right), rest671)
end
|  ( 24, ( ( _, ( _, _, END1right)) :: _ :: ( _, ( MlyValue.decs decs1
, _, _)) :: ( _, ( _, (LETleft as LET1left), _)) :: rest671)) => let
 val  result = MlyValue.exp (fn _ => let val  (decs as decs1) = decs1
 ()
 in (
A.LetExp {decs = decs, body = (A.SeqExp nil), 
                                   pos = LETleft}
)
end)
 in ( LrTable.NT 1, ( result, LET1left, END1right), rest671)
end
|  ( 25, ( ( _, ( _, _, END1right)) :: ( _, ( MlyValue.expseq expseq1,
 _, _)) :: _ :: ( _, ( MlyValue.decs decs1, _, _)) :: ( _, ( _, (
LETleft as LET1left), _)) :: rest671)) => let val  result = 
MlyValue.exp (fn _ => let val  (decs as decs1) = decs1 ()
 val  (expseq as expseq1) = expseq1 ()
 in (
A.LetExp {decs = decs, body = (A.SeqExp expseq), 
                                   pos = LETleft}
)
end)
 in ( LrTable.NT 1, ( result, LET1left, END1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.lvaluerest lvaluerest1, _, lvaluerest1right
)) :: ( _, ( MlyValue.ID ID1, (IDleft as ID1left), _)) :: rest671)) =>
 let val  result = MlyValue.lvalue (fn _ => let val  (ID as ID1) = ID1
 ()
 val  (lvaluerest as lvaluerest1) = lvaluerest1 ()
 in (
lvaluerest (A.SimpleVar ((Symbol.symbol ID),
                                                   IDleft))
)
end)
 in ( LrTable.NT 2, ( result, ID1left, lvaluerest1right), rest671)
end
|  ( 27, ( rest671)) => let val  result = MlyValue.lvaluerest (fn _ =>
 (fn x => x))
 in ( LrTable.NT 3, ( result, defaultPos, defaultPos), rest671)
end
|  ( 28, ( ( _, ( MlyValue.lvaluerest lvaluerest1, _, lvaluerest1right
)) :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, (DOTleft as DOT1left
), _)) :: rest671)) => let val  result = MlyValue.lvaluerest (fn _ =>
 let val  (ID as ID1) = ID1 ()
 val  (lvaluerest as lvaluerest1) = lvaluerest1 ()
 in (
fn x => (lvaluerest (A.FieldVar 
                                                      (x,(Symbol.symbol ID),
                                                       DOTleft)))
)
end)
 in ( LrTable.NT 3, ( result, DOT1left, lvaluerest1right), rest671)

end
|  ( 29, ( ( _, ( MlyValue.lvaluerest lvaluerest1, _, lvaluerest1right
)) :: _ :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, ( _, (LBRACKleft
 as LBRACK1left), _)) :: rest671)) => let val  result = 
MlyValue.lvaluerest (fn _ => let val  (exp as exp1) = exp1 ()
 val  (lvaluerest as lvaluerest1) = lvaluerest1 ()
 in (
fn x => (lvaluerest (A.SubscriptVar 
                                                    (x,exp,LBRACKleft)))
)
end)
 in ( LrTable.NT 3, ( result, LBRACK1left, lvaluerest1right), rest671)

end
|  ( 30, ( ( _, ( MlyValue.exps exps1, _, exps1right)) :: _ :: ( _, ( 
MlyValue.exp exp1, (expleft as exp1left), _)) :: rest671)) => let val 
 result = MlyValue.expseq (fn _ => let val  (exp as exp1) = exp1 ()
 val  (exps as exps1) = exps1 ()
 in ((exp,expleft) :: exps)
end)
 in ( LrTable.NT 4, ( result, exp1left, exps1right), rest671)
end
|  ( 31, ( ( _, ( MlyValue.exp exp1, (expleft as exp1left), exp1right)
) :: rest671)) => let val  result = MlyValue.exps (fn _ => let val  (
exp as exp1) = exp1 ()
 in ([(exp,expleft)])
end)
 in ( LrTable.NT 5, ( result, exp1left, exp1right), rest671)
end
|  ( 32, ( ( _, ( MlyValue.exps exps1, _, exps1right)) :: _ :: ( _, ( 
MlyValue.exp exp1, (expleft as exp1left), _)) :: rest671)) => let val 
 result = MlyValue.exps (fn _ => let val  (exp as exp1) = exp1 ()
 val  (exps as exps1) = exps1 ()
 in ((exp,expleft) :: exps)
end)
 in ( LrTable.NT 5, ( result, exp1left, exps1right), rest671)
end
|  ( 33, ( ( _, ( MlyValue.argsplus argsplus1, _, argsplus1right)) :: 
( _, ( MlyValue.exp exp1, exp1left, _)) :: rest671)) => let val  
result = MlyValue.funargs (fn _ => let val  (exp as exp1) = exp1 ()
 val  (argsplus as argsplus1) = argsplus1 ()
 in (exp :: argsplus)
end)
 in ( LrTable.NT 6, ( result, exp1left, argsplus1right), rest671)
end
|  ( 34, ( rest671)) => let val  result = MlyValue.funargs (fn _ => (
nil))
 in ( LrTable.NT 6, ( result, defaultPos, defaultPos), rest671)
end
|  ( 35, ( ( _, ( MlyValue.argsplus argsplus1, _, argsplus1right)) :: 
( _, ( MlyValue.exp exp1, _, _)) :: ( _, ( _, COMMA1left, _)) :: 
rest671)) => let val  result = MlyValue.argsplus (fn _ => let val  (
exp as exp1) = exp1 ()
 val  (argsplus as argsplus1) = argsplus1 ()
 in (exp :: argsplus)
end)
 in ( LrTable.NT 7, ( result, COMMA1left, argsplus1right), rest671)

end
|  ( 36, ( rest671)) => let val  result = MlyValue.argsplus (fn _ => (
nil))
 in ( LrTable.NT 7, ( result, defaultPos, defaultPos), rest671)
end
|  ( 37, ( ( _, ( MlyValue.recinitsplus recinitsplus1, _, 
recinitsplus1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, ( _, 
EQleft, _)) :: ( _, ( MlyValue.ID ID1, ID1left, _)) :: rest671)) =>
 let val  result = MlyValue.recinits (fn _ => let val  (ID as ID1) = 
ID1 ()
 val  (exp as exp1) = exp1 ()
 val  (recinitsplus as recinitsplus1) = recinitsplus1 ()
 in (((Symbol.symbol ID),exp,EQleft) :: recinitsplus)
end)
 in ( LrTable.NT 8, ( result, ID1left, recinitsplus1right), rest671)

end
|  ( 38, ( rest671)) => let val  result = MlyValue.recinits (fn _ => (
nil))
 in ( LrTable.NT 8, ( result, defaultPos, defaultPos), rest671)
end
|  ( 39, ( ( _, ( MlyValue.recinitsplus recinitsplus1, _, 
recinitsplus1right)) :: ( _, ( MlyValue.exp exp1, _, _)) :: ( _, ( _, 
EQleft, _)) :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, COMMA1left,
 _)) :: rest671)) => let val  result = MlyValue.recinitsplus (fn _ =>
 let val  (ID as ID1) = ID1 ()
 val  (exp as exp1) = exp1 ()
 val  (recinitsplus as recinitsplus1) = recinitsplus1 ()
 in (((Symbol.symbol ID),exp,EQleft) :: recinitsplus)
end)
 in ( LrTable.NT 9, ( result, COMMA1left, recinitsplus1right), rest671
)
end
|  ( 40, ( rest671)) => let val  result = MlyValue.recinitsplus (fn _
 => (nil))
 in ( LrTable.NT 9, ( result, defaultPos, defaultPos), rest671)
end
|  ( 41, ( ( _, ( _, TIMES1left, TIMES1right)) :: rest671)) => let
 val  result = MlyValue.multop (fn _ => (A.TimesOp))
 in ( LrTable.NT 10, ( result, TIMES1left, TIMES1right), rest671)
end
|  ( 42, ( ( _, ( _, DIVIDE1left, DIVIDE1right)) :: rest671)) => let
 val  result = MlyValue.multop (fn _ => (A.DivideOp))
 in ( LrTable.NT 10, ( result, DIVIDE1left, DIVIDE1right), rest671)

end
|  ( 43, ( ( _, ( _, PLUS1left, PLUS1right)) :: rest671)) => let val  
result = MlyValue.addop (fn _ => (A.PlusOp))
 in ( LrTable.NT 11, ( result, PLUS1left, PLUS1right), rest671)
end
|  ( 44, ( ( _, ( _, MINUS1left, MINUS1right)) :: rest671)) => let
 val  result = MlyValue.addop (fn _ => (A.MinusOp))
 in ( LrTable.NT 11, ( result, MINUS1left, MINUS1right), rest671)
end
|  ( 45, ( ( _, ( _, EQ1left, EQ1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.EqOp))
 in ( LrTable.NT 12, ( result, EQ1left, EQ1right), rest671)
end
|  ( 46, ( ( _, ( _, NEQ1left, NEQ1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.NeqOp))
 in ( LrTable.NT 12, ( result, NEQ1left, NEQ1right), rest671)
end
|  ( 47, ( ( _, ( _, LT1left, LT1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.LtOp))
 in ( LrTable.NT 12, ( result, LT1left, LT1right), rest671)
end
|  ( 48, ( ( _, ( _, LE1left, LE1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.LeOp))
 in ( LrTable.NT 12, ( result, LE1left, LE1right), rest671)
end
|  ( 49, ( ( _, ( _, GT1left, GT1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.GtOp))
 in ( LrTable.NT 12, ( result, GT1left, GT1right), rest671)
end
|  ( 50, ( ( _, ( _, GE1left, GE1right)) :: rest671)) => let val  
result = MlyValue.compop (fn _ => (A.GeOp))
 in ( LrTable.NT 12, ( result, GE1left, GE1right), rest671)
end
|  ( 51, ( rest671)) => let val  result = MlyValue.decs (fn _ => (nil)
)
 in ( LrTable.NT 13, ( result, defaultPos, defaultPos), rest671)
end
|  ( 52, ( ( _, ( MlyValue.decs decs1, _, decs1right)) :: ( _, ( 
MlyValue.vardec vardec1, vardec1left, _)) :: rest671)) => let val  
result = MlyValue.decs (fn _ => let val  (vardec as vardec1) = vardec1
 ()
 val  (decs as decs1) = decs1 ()
 in (vardec :: decs)
end)
 in ( LrTable.NT 13, ( result, vardec1left, decs1right), rest671)
end
|  ( 53, ( ( _, ( MlyValue.followtydecs followtydecs1, _, 
followtydecs1right)) :: ( _, ( MlyValue.tydecs tydecs1, tydecs1left, _
)) :: rest671)) => let val  result = MlyValue.decs (fn _ => let val  (
tydecs as tydecs1) = tydecs1 ()
 val  (followtydecs as followtydecs1) = followtydecs1 ()
 in ((A.TypeDec tydecs) :: followtydecs)
end)
 in ( LrTable.NT 13, ( result, tydecs1left, followtydecs1right), 
rest671)
end
|  ( 54, ( ( _, ( MlyValue.followfundecs followfundecs1, _, 
followfundecs1right)) :: ( _, ( MlyValue.fundecs fundecs1, 
fundecs1left, _)) :: rest671)) => let val  result = MlyValue.decs (fn
 _ => let val  (fundecs as fundecs1) = fundecs1 ()
 val  (followfundecs as followfundecs1) = followfundecs1 ()
 in ((A.FunctionDec fundecs) :: followfundecs)
end)
 in ( LrTable.NT 13, ( result, fundecs1left, followfundecs1right), 
rest671)
end
|  ( 55, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, (VARleft as VAR1left), _)) :: 
rest671)) => let val  result = MlyValue.vardec (fn _ => let val  (ID
 as ID1) = ID1 ()
 val  (exp as exp1) = exp1 ()
 in (
A.VarDec {name = (Symbol.symbol ID), 
                                   escape = (ref true),
                                   typ = NONE, init = exp, pos = VARleft}
)
end)
 in ( LrTable.NT 20, ( result, VAR1left, exp1right), rest671)
end
|  ( 56, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID2, ID2left, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _))
 :: ( _, ( _, (VARleft as VAR1left), _)) :: rest671)) => let val  
result = MlyValue.vardec (fn _ => let val  ID1 = ID1 ()
 val  ID2 = ID2 ()
 val  (exp as exp1) = exp1 ()
 in (
A.VarDec {name = (Symbol.symbol ID1), 
                                   escape = (ref true),
                                   typ = (SOME ((Symbol.symbol ID2),ID2left)),
                                   init = exp, pos = VARleft}
)
end)
 in ( LrTable.NT 20, ( result, VAR1left, exp1right), rest671)
end
|  ( 57, ( ( _, ( MlyValue.tydec tydec1, tydec1left, tydec1right)) :: 
rest671)) => let val  result = MlyValue.tydecs (fn _ => let val  (
tydec as tydec1) = tydec1 ()
 in ([tydec])
end)
 in ( LrTable.NT 14, ( result, tydec1left, tydec1right), rest671)
end
|  ( 58, ( ( _, ( MlyValue.tydecs tydecs1, _, tydecs1right)) :: ( _, (
 MlyValue.tydec tydec1, tydec1left, _)) :: rest671)) => let val  
result = MlyValue.tydecs (fn _ => let val  (tydec as tydec1) = tydec1
 ()
 val  (tydecs as tydecs1) = tydecs1 ()
 in (tydec :: tydecs)
end)
 in ( LrTable.NT 14, ( result, tydec1left, tydecs1right), rest671)
end
|  ( 59, ( ( _, ( MlyValue.ty ty1, _, ty1right)) :: _ :: ( _, ( 
MlyValue.ID ID1, _, _)) :: ( _, ( _, (TYPEleft as TYPE1left), _)) :: 
rest671)) => let val  result = MlyValue.tydec (fn _ => let val  (ID
 as ID1) = ID1 ()
 val  (ty as ty1) = ty1 ()
 in ({name = (Symbol.symbol ID), ty = ty, pos = TYPEleft})
end)
 in ( LrTable.NT 15, ( result, TYPE1left, ty1right), rest671)
end
|  ( 60, ( ( _, ( MlyValue.ID ID1, (IDleft as ID1left), ID1right)) :: 
rest671)) => let val  result = MlyValue.ty (fn _ => let val  (ID as 
ID1) = ID1 ()
 in (A.NameTy ((Symbol.symbol ID),IDleft))
end)
 in ( LrTable.NT 17, ( result, ID1left, ID1right), rest671)
end
|  ( 61, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.fields 
fields1, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let val 
 result = MlyValue.ty (fn _ => let val  (fields as fields1) = fields1
 ()
 in (A.RecordTy fields)
end)
 in ( LrTable.NT 17, ( result, LBRACE1left, RBRACE1right), rest671)

end
|  ( 62, ( ( _, ( MlyValue.ID ID1, IDleft, ID1right)) :: _ :: ( _, ( _
, ARRAY1left, _)) :: rest671)) => let val  result = MlyValue.ty (fn _
 => let val  (ID as ID1) = ID1 ()
 in (A.ArrayTy ((Symbol.symbol ID),IDleft))
end)
 in ( LrTable.NT 17, ( result, ARRAY1left, ID1right), rest671)
end
|  ( 63, ( ( _, ( MlyValue.fieldsplus fieldsplus1, _, fieldsplus1right
)) :: ( _, ( MlyValue.ID ID2, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, 
ID1left, _)) :: rest671)) => let val  result = MlyValue.fields (fn _
 => let val  ID1 = ID1 ()
 val  ID2 = ID2 ()
 val  (fieldsplus as fieldsplus1) = fieldsplus1 ()
 in (
{name = (Symbol.symbol ID1), escape = (ref true),
                          typ = (Symbol.symbol ID2), pos = ID1left} ::
                             fieldsplus
)
end)
 in ( LrTable.NT 18, ( result, ID1left, fieldsplus1right), rest671)

end
|  ( 64, ( rest671)) => let val  result = MlyValue.fields (fn _ => (
nil))
 in ( LrTable.NT 18, ( result, defaultPos, defaultPos), rest671)
end
|  ( 65, ( ( _, ( MlyValue.fieldsplus fieldsplus1, _, fieldsplus1right
)) :: ( _, ( MlyValue.ID ID2, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, 
ID1left, _)) :: ( _, ( _, COMMA1left, _)) :: rest671)) => let val  
result = MlyValue.fieldsplus (fn _ => let val  ID1 = ID1 ()
 val  ID2 = ID2 ()
 val  (fieldsplus as fieldsplus1) = fieldsplus1 ()
 in (
{name = (Symbol.symbol ID1), escape = (ref true),
                          typ = (Symbol.symbol ID2), pos = ID1left} ::
                             fieldsplus
)
end)
 in ( LrTable.NT 19, ( result, COMMA1left, fieldsplus1right), rest671)

end
|  ( 66, ( rest671)) => let val  result = MlyValue.fieldsplus (fn _ =>
 (nil))
 in ( LrTable.NT 19, ( result, defaultPos, defaultPos), rest671)
end
|  ( 67, ( rest671)) => let val  result = MlyValue.followtydecs (fn _
 => (nil))
 in ( LrTable.NT 16, ( result, defaultPos, defaultPos), rest671)
end
|  ( 68, ( ( _, ( MlyValue.decs decs1, _, decs1right)) :: ( _, ( 
MlyValue.vardec vardec1, vardec1left, _)) :: rest671)) => let val  
result = MlyValue.followtydecs (fn _ => let val  (vardec as vardec1) =
 vardec1 ()
 val  (decs as decs1) = decs1 ()
 in (vardec :: decs)
end)
 in ( LrTable.NT 16, ( result, vardec1left, decs1right), rest671)
end
|  ( 69, ( ( _, ( MlyValue.followfundecs followfundecs1, _, 
followfundecs1right)) :: ( _, ( MlyValue.fundecs fundecs1, 
fundecs1left, _)) :: rest671)) => let val  result = 
MlyValue.followtydecs (fn _ => let val  (fundecs as fundecs1) = 
fundecs1 ()
 val  (followfundecs as followfundecs1) = followfundecs1 ()
 in ((A.FunctionDec fundecs) :: followfundecs)
end)
 in ( LrTable.NT 16, ( result, fundecs1left, followfundecs1right), 
rest671)
end
|  ( 70, ( ( _, ( MlyValue.fundec fundec1, fundec1left, fundec1right))
 :: rest671)) => let val  result = MlyValue.fundecs (fn _ => let val 
 (fundec as fundec1) = fundec1 ()
 in ([fundec])
end)
 in ( LrTable.NT 21, ( result, fundec1left, fundec1right), rest671)

end
|  ( 71, ( ( _, ( MlyValue.fundecs fundecs1, _, fundecs1right)) :: ( _
, ( MlyValue.fundec fundec1, fundec1left, _)) :: rest671)) => let val 
 result = MlyValue.fundecs (fn _ => let val  (fundec as fundec1) = 
fundec1 ()
 val  (fundecs as fundecs1) = fundecs1 ()
 in (fundec :: fundecs)
end)
 in ( LrTable.NT 21, ( result, fundec1left, fundecs1right), rest671)

end
|  ( 72, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: _ :: ( _, 
( MlyValue.fields fields1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _
)) :: ( _, ( _, (FUNCTIONleft as FUNCTION1left), _)) :: rest671)) =>
 let val  result = MlyValue.fundec (fn _ => let val  (ID as ID1) = ID1
 ()
 val  (fields as fields1) = fields1 ()
 val  (exp as exp1) = exp1 ()
 in (
{name = (Symbol.symbol ID), params = fields,
                          result = NONE, body = exp, pos = FUNCTIONleft}
)
end)
 in ( LrTable.NT 22, ( result, FUNCTION1left, exp1right), rest671)
end
|  ( 73, ( ( _, ( MlyValue.exp exp1, _, exp1right)) :: _ :: ( _, ( 
MlyValue.ID ID2, ID2left, _)) :: _ :: _ :: ( _, ( MlyValue.fields 
fields1, _, _)) :: _ :: ( _, ( MlyValue.ID ID1, _, _)) :: ( _, ( _, (
FUNCTIONleft as FUNCTION1left), _)) :: rest671)) => let val  result = 
MlyValue.fundec (fn _ => let val  ID1 = ID1 ()
 val  (fields as fields1) = fields1 ()
 val  ID2 = ID2 ()
 val  (exp as exp1) = exp1 ()
 in (
{name = (Symbol.symbol ID1), params = fields,
                          result = (SOME ((Symbol.symbol ID2),ID2left)), 
                          body = exp, pos = FUNCTIONleft}
)
end)
 in ( LrTable.NT 22, ( result, FUNCTION1left, exp1right), rest671)
end
|  ( 74, ( rest671)) => let val  result = MlyValue.followfundecs (fn _
 => (nil))
 in ( LrTable.NT 23, ( result, defaultPos, defaultPos), rest671)
end
|  ( 75, ( ( _, ( MlyValue.decs decs1, _, decs1right)) :: ( _, ( 
MlyValue.vardec vardec1, vardec1left, _)) :: rest671)) => let val  
result = MlyValue.followfundecs (fn _ => let val  (vardec as vardec1)
 = vardec1 ()
 val  (decs as decs1) = decs1 ()
 in (vardec :: decs)
end)
 in ( LrTable.NT 23, ( result, vardec1left, decs1right), rest671)
end
|  ( 76, ( ( _, ( MlyValue.followtydecs followtydecs1, _, 
followtydecs1right)) :: ( _, ( MlyValue.tydecs tydecs1, tydecs1left, _
)) :: rest671)) => let val  result = MlyValue.followfundecs (fn _ =>
 let val  (tydecs as tydecs1) = tydecs1 ()
 val  (followtydecs as followtydecs1) = followtydecs1 ()
 in ((A.TypeDec tydecs) :: followtydecs)
end)
 in ( LrTable.NT 23, ( result, tydecs1left, followtydecs1right), 
rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.program x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Tiger_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.ID (fn () => i),p1,p2))
fun INT (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.INT (fn () => i),p1,p2))
fun STRING (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.STRING (fn () => i),p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun COLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun SEMICOLON (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(
ParserData.MlyValue.VOID,p1,p2))
fun DOT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(
ParserData.MlyValue.VOID,p1,p2))
fun OR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(
ParserData.MlyValue.VOID,p1,p2))
fun AND (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(
ParserData.MlyValue.VOID,p1,p2))
fun EQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(
ParserData.MlyValue.VOID,p1,p2))
fun NEQ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(
ParserData.MlyValue.VOID,p1,p2))
fun LT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(
ParserData.MlyValue.VOID,p1,p2))
fun LE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(
ParserData.MlyValue.VOID,p1,p2))
fun GT (p1,p2) = Token.TOKEN (ParserData.LrTable.T 20,(
ParserData.MlyValue.VOID,p1,p2))
fun GE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 21,(
ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 22,(
ParserData.MlyValue.VOID,p1,p2))
fun MINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 23,(
ParserData.MlyValue.VOID,p1,p2))
fun TIMES (p1,p2) = Token.TOKEN (ParserData.LrTable.T 24,(
ParserData.MlyValue.VOID,p1,p2))
fun DIVIDE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 25,(
ParserData.MlyValue.VOID,p1,p2))
fun UMINUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 26,(
ParserData.MlyValue.VOID,p1,p2))
fun ASSIGN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 27,(
ParserData.MlyValue.VOID,p1,p2))
fun ARRAY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 28,(
ParserData.MlyValue.VOID,p1,p2))
fun IF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 29,(
ParserData.MlyValue.VOID,p1,p2))
fun THEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 30,(
ParserData.MlyValue.VOID,p1,p2))
fun ELSE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 31,(
ParserData.MlyValue.VOID,p1,p2))
fun WHILE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 32,(
ParserData.MlyValue.VOID,p1,p2))
fun FOR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 33,(
ParserData.MlyValue.VOID,p1,p2))
fun TO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 34,(
ParserData.MlyValue.VOID,p1,p2))
fun DO (p1,p2) = Token.TOKEN (ParserData.LrTable.T 35,(
ParserData.MlyValue.VOID,p1,p2))
fun LET (p1,p2) = Token.TOKEN (ParserData.LrTable.T 36,(
ParserData.MlyValue.VOID,p1,p2))
fun IN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 37,(
ParserData.MlyValue.VOID,p1,p2))
fun END (p1,p2) = Token.TOKEN (ParserData.LrTable.T 38,(
ParserData.MlyValue.VOID,p1,p2))
fun OF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 39,(
ParserData.MlyValue.VOID,p1,p2))
fun BREAK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 40,(
ParserData.MlyValue.VOID,p1,p2))
fun NIL (p1,p2) = Token.TOKEN (ParserData.LrTable.T 41,(
ParserData.MlyValue.VOID,p1,p2))
fun FUNCTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 42,(
ParserData.MlyValue.VOID,p1,p2))
fun VAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 43,(
ParserData.MlyValue.VOID,p1,p2))
fun TYPE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 44,(
ParserData.MlyValue.VOID,p1,p2))
end
end
