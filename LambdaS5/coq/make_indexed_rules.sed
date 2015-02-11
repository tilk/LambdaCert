# change the name of the predicate
s/red_expr/red_exprh/g
# add the natural "depth" parameter
s/Inductive red_exprh : /Inductive red_exprh : nat -> /g
# add the parameter to quantifiers
s/forall c/forall k c/g
# add the parameter in the definition
s/red_exprh c/red_exprh k c/g
# increment the parameter, but only on the "big" steps
s/red_exprh k c st (\(?expr_([a-z_]*|op[12])[ \)])/red_exprh (S k) c st \1/g
