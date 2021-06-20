# Co-inductive big-step semantics for IMP
## Formalizacja języków programowania w Coqu: Miniprojekt

### Zawartość:
`Maps.v` i `Imp.v` pochodzą z `Software Foundations: Logical Foundations`.
`CoImp.v` zawiera definicje koindukcyjnych semantyk dużych kroków dla IMPa, przygotowany na podstawie pracy [Coinductive big-step operational semantics](https://www.sciencedirect.com/science/article/pii/S0890540108001296) autorstwa Xaviera Leroy i Hervé Gralla oraz jej [formalizacji w Coqu](https://xavierleroy.org/coindsem/).

## Semantyka
Mamy indukcyjną relację `eval` z `SF` (oryginalnie `ceval`).
```Coq
st =[ c ]=> st'

                           -----------------                            (C_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                       (C_Ass)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ------------------==-                           (C_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------                (C_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------               (C_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (C_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (C_WhileTrue)
                  st  =[ while b do c end ]=> st''
```

Zdefiniowałem koindukcyjną relację `evalinf`, która oznacza że ewaluacja danej komendy w określonym stanie nie kończy się:
```Coq
st =[ c ]=>inf

                           st =[ c1 ]=>inf
                         ======================                         (I_Seq1)
                         st =[ c1;c2 ]=>inf

                          s t =[ c1 ]=> st'
                          st' =[ c2 ]=>inf
                         =====================                          (I_Seq2)
                         st =[ c1;c2 ]=>inf

                          beval st b = true
                           st =[ c1 ]=>inf
                ======================================                (I_IfTrue)
                st =[ if b then c1 else c2 end ]=>inf

                         beval st b = false
                           st =[ c2 ]=>inf
                ======================================               (I_IfFalse)
                st =[ if b then c1 else c2 end ]=>inf

                         beval st b = true
                           st =[ c ]=>inf
                    =============================                  (I_WhileBody)
                    st =[ while b do c end ]=>inf

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=>inf
                  ================================                 (I_WhileTrue)
                  st  =[ while b do c end ]=>inf

```

Oraz koindukcyjnę relację `coeval`, analogiczną do `eval`.
```Coq
st =[ c ]=>> st'

                           =================                            (C_Skip)
                           st =[ skip ]=>> st

                           aeval st a = n
                   ===============================                       (C_Ass)
                   st =[ x := a ]=>> (x !-> n ; st)

                           st  =[ c1 ]=>> st'
                           st' =[ c2 ]=>> st''
                         ====================-                           (C_Seq)
                         st =[ c1;c2 ]=>> st''

                          beval st b = true
                           st =[ c1 ]=>> st'
                ======================================                (C_IfTrue)
                st =[ if b then c1 else c2 end ]=>> st'

                         beval st b = false
                           st =[ c2 ]=>> st'
                ======================================               (C_IfFalse)
                st =[ if b then c1 else c2 end ]=>> st'

                         beval st b = false
                    =============================                 (C_WhileFalse)
                    st =[ while b do c end ]=>> st

                          beval st b = true
                           st =[ c ]=>> st'
                  st' =[ while b do c end ]=>> st''
                  ================================                 (C_WhileTrue)
                  st  =[ while b do c end ]=>> st''
```

## Własności semantyki

W `CoImp.v` znajdują się dowody następujących własności:

```Coq
Theorem eval_coeval: forall c st st',
    st =[ c ]=> st' ->
    st =[ c ]=>> st'.

Theorem coeval_eval_or_evalinf: forall c st st',
    st =[ c ]=>> st' ->
    st =[ c ]=> st' \/ st =[ c ]=>inf.

Theorem eval_coeval_deterministic: forall c st st',
    st =[ c ]=> st' ->
    forall st'', st =[ c ]=>> st''-> st' = st''.
```