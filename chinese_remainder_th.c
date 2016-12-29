//@ #include "arith.gh"
//@ #include <nat.gh>

/*@

predicate coprime(nat n1, nat n2) = true;

fixpoint bool equals_modulo(nat mod, nat a, nat b) 
{
  return int_of_nat(a) % int_of_nat(mod) == int_of_nat(b) % int_of_nat(mod);
}

fixpoint bool CRT_val(nat mod1, nat a1, nat mod2, nat a2, nat x)
{
  return equals_modulo(mod1, a1, x) && equals_modulo(mod2, a2, x);
}

fixpoint bool n_at_nth(list<nat> lst, nat n)
{
  return nth(int_of_nat(n), lst) == n;
}

fixpoint bool n_plus_base_at_nth(list<nat> lst, nat base, nat n)
{
  return nth(int_of_nat(n), lst) == nat_of_int(int_of_nat(n) + int_of_nat(base));
}

lemma list<nat> generate_ints(nat length, nat base)
requires true;
ensures forall(result, (n_plus_base_at_nth)(result, base)) == true &*& length(result) == int_of_nat(length);
{
  switch(length) {
    case zero: return nil;
    case succ(p_length): {
      list<nat> lst0 = generate_ints(p_length, succ(base));
      list<nat> lst = cons(base, lst0);
      
      if(forall(lst, (n_plus_base_at_nth)(lst, base)) == false)
      {
        
      }
      return lst;
    }
  }
}

lemma list<nat> bin_chinese_remainder_theorem(nat n1, nat a1, nat n2, nat a2)
requires coprime(n1, n2);
ensures exists(result, (CRT_val)(n1, a1, n2, a2)) == true &*& forall(result, (n_at_nth)(result)) == true &*& length(result) == int_of_nat(n1) * int_of_nat(n2);
{
  
}

@*/ 