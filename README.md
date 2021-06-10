# Co-inductive big-step semantics for IMP
## Formalizacja języków programowania w Coqu: Miniprojekt

### Zawartość:
`Maps.v` i `Imp.v` pochodzą z `Software Foundations: Logical Foundations`.
`CoImp.v` zawiera definicje koindukcyjnych semantyk dużych kroków dla IMPa, który przygotowałem na podstawie pracy [Coinductive big-step operational semantics](https://www.sciencedirect.com/science/article/pii/S0890540108001296) autorstwa Xaviera Leroy i Hervé Gralla oraz jej [formalizacji w Coqu](https://xavierleroy.org/coindsem/).

## Semantyka
Mamy indukcyjną relację `eval` z `SF` (oryginalnie `ceval`).
```Coq
st =[ c ]=> st'
```

Zdefiniowałem koindukcyjną relację `evalinf`, która oznacza że ewaluacja danej komendy w określonym stanie nie kończy się:
```Coq
st =[ c ]=>inf
```

Oraz koindukcyjnę relację `coeval`, analogiczną do `eval`.
```Coq
st =[ c ]=> st'
```

## Własności `eval`, `evalinf` i `coeval`

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