/*! 
\title{FPL}

\author{Lars Hansen}
*/

module FPL-SYNTAX
  
  syntax Exp ::= Val
               | Id
               | "halt"
               | Exp "*" Exp [left,strict]
               | Exp "/" Exp [left,strict]
               > Exp "+" Exp [left,strict]
               | Exp "-" Exp [left,strict]
               > Exp "<" Exp [strict]
               > "empty" "(" Exp ")" [strict]
               | "hd" "(" Exp ")" [strict]
               | "tl" "(" Exp ")" [strict]
               > Exp "(" Exps ")" [strict]
               | Lambda
               > LiExp
               | Id ":=" Exp [right,strict(2)]
               > "if" Exp "then" Block "else" Block [strict(1)]
               | Funct
               > Exp ";" Exp [left]
               | "(" Exp ")" [bracket]

  syntax Exps ::= List{Exp,","} [strict]

  syntax Ids ::= List{Id, ","}

  syntax Funct ::= "def" Id "(" Ids ")" Block
  syntax Lambda ::= "lambda" Ids "->" Block

  syntax Block ::= "{" Exp "}" | "{" "}"

  syntax Li ::= "[" Vals "]"
  syntax LiExp ::= Li
                 | "[" Exps "]" [strict]
                 | Exp ":" LiExp [right,strict]

  syntax Val ::= Int | Bool | String | Lambda | Li
  syntax Vals ::= List{Val,","}
endmodule

module FPL-CONFIG
  imports FPL-SYNTAX

  syntax KResult ::= Val

  configuration
    <T>
      <k color="green"> $PGM:K </k>
      <env color="yellow"> .Map </env>
      <store color="red"> .Map </store>
      <fstack color="blue"> .List </fstack>
      <genv color="orange"> .Map </genv>
      <ans> false </ans>
    </T>
endmodule

module FPL
  imports FPL-CONFIG

  // sequential composition
  rule X:Exp ; Y:Exp => X ~> Y [structural]

  // halting
  rule <k> halt ~> K => . </k>
       //<trace> .=> K </trace>

  // delete non-used Values
  rule <k> V:Val ~> E => E ... </k>
       <ans> _ => V </ans>


  // std integer operations
  rule X:Int + Y:Int => X +Int Y
  rule X:Int - Y:Int => X -Int Y
  rule X:Int * Y:Int => X *Int Y
  rule X:Int / Y:Int => X /Int Y
    when Y =/=Int 0

  // comparison
  rule X:Int < Y:Int => X <Int Y

  // list extension
  rule V:Val : [Vs:Vals] => [V,Vs]

  // list operations
  rule empty([.Vals]) => true
  rule empty([V:Val,Vs:Vals]) => false
  rule hd([V:Val,Vs:Vals]) => V
  rule tl([V:Val,Vs:Vals]) => [Vs]

  // conditional
  rule if true then B:Block else _ => B
  rule if false then _ else B:Block => B

  // function definition
  rule <k> def N:Id ( Args:Ids ) B:Block => . ... </k>
       <env> E => E[L/N] </env>
       <genv> E => E[L/N] </genv>
       <store> ... .=>(L |-> lambda Args -> B) </store>
    when fresh(L)

  // lambda definition
  // not necessary!

  // variable definition
  rule <k> (N:Id := V:Val) => V ... </k>
       <env> E => E[L/N] </env>
       <store> ... .=>(L|->V) </store>
    when fresh(L)

  // variable lookup
  rule <k> N:Id => V ... </k>
      <env> ... N |-> L ...</env>
      <store>... L |-> V:Val ...</store>
    [transition]

  // lambda application
  syntax K ::= (Map, K)
  syntax K ::= "return"
  // partial application
  rule lambda X:Id,Args:Ids -> { E:Exp } ( V:Val,Vs:Vals )
        => lambda Args -> { (X:=V);E } (Vs)
  rule lambda X:Id,Args:Ids -> B:Block ( .Vals ) => lambda X,Args -> B
  // execute TODO why is this necessary? remove
  rule lambda .Ids -> B:Block ( .Vals ) => B
  // execute
  rule <k> (lambda .Ids -> B:Block ( .Vals ) ~> K) => (B ~> return) ... </k>
       <env> Env => GEnv </env>
       <genv> GEnv </genv>
       <fstack> .=> ListItem((Env,K)) ... </fstack>

  // block execution
  rule { Exp } => Exp

  // return
  rule <k> return ~> _ => V ~> K </k>
       <env> _ => Env </env>
       <fstack> ListItem((Env, K)) =>. ... </fstack>
       <ans> V </ans>

endmodule
