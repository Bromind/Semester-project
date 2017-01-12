#include "map_generator.h"
//#include "include_ignored_by_verifast.h"
//#include "lib/ignore.h"

//@ #include <list.gh>
//@ #include <listex.gh>
//@ #include <nat.gh>
//@ #include "stdex.gh"
//@ #include "nth_prop.gh"
//@ #include "modulo.gh"
//@ #include "chinese_remainder_th.gh"
//@ #include "up_to_conversions.gh"

/*@


 fixpoint bool is_n(nat n, nat i) {
   return n == i;
 }
 
 fixpoint bool is_none(option<nat> opt)
 {
   return opt == none;
 }
 
 fixpoint bool is_some(option<nat> opt)
 {
   return !is_none(opt);
 }
 
 fixpoint bool is_zero(nat n) {
   return is_n(zero, n);
 }
 
 fixpoint bool is_not_zero(nat n) {
  return is_n(zero, n) == true ? false : true;
 }

 fixpoint list<option<nat> > gen_none(nat capa)
 {
   switch(capa) {
     case(zero): return nil;
     case succ(p_capa): return cons(none, gen_none(p_capa));
   }
 }
 
  
 fixpoint bool opt_less_than_n(nat n, option<nat> opt_i)
 {
   switch(opt_i) {
     case none: return true;
     case some(i): return int_of_nat(n) >= int_of_nat(i);
   }
 }
 
 fixpoint bool opt_not_zero(option<nat> opt_i)
 {
   switch(opt_i) {
     case none: return true;
     case some(i): return i != zero;
   }
 }
 
 fixpoint bool lst_opt_less_than_n(list<option<nat> > lst, nat n, int index)
 {
   return opt_less_than_n(n, nth(index, lst));
 }
 
 fixpoint bool lst_opt_not_zero(list<option<nat> > lst, int index)
 {
   return opt_not_zero(nth(index, lst));
 }
  
 lemma void gen_none_less_than(nat capa, nat n)
 requires true;
 ensures true == forall(gen_none(capa), (opt_less_than_n)(n));
 {
   switch(capa) {
     case(zero): ;
     case succ(p_capa): gen_none_less_than(p_capa, n);
   }
 }
 
 lemma void gen_none_l(nat capa)
 requires true;
 ensures length(gen_none(capa)) == int_of_nat(capa)
 	&*& true == forall(gen_none(capa), is_none) 
 	&*& count_some(gen_none(capa)) == zero
 	&*& true == forall(gen_none(capa), opt_not_zero);
 {
   switch(capa) {
     case(zero): ;
     case succ(p_capa): gen_none_l(p_capa);
   }
 }

 fixpoint nat count_some(list<option<nat> > lst) {
   switch(lst) {
     case nil: return zero;
     case cons(hd, tl): return hd == none ? count_some(tl) : succ(count_some(tl));
   }
 }
 
 lemma void count_some_less_than_length(list<option<nat> > lst)
 requires true;
 ensures int_of_nat(count_some(lst)) <= length(lst);
 {
   switch(lst) {
     case nil:
     case cons(hd, tl): count_some_less_than_length(tl);
   }
 }
 
 lemma void count_some_forall(list<option<nat> > lst)
 requires count_some(lst) == nat_of_int(length(lst));
 ensures true == forall(lst, is_some);
 {
   switch(lst){
     case nil: 
     case cons(hd, tl): {
       if(is_some(hd) == false){
         count_some_less_than_length(tl);
         assert false;
       }
       assert count_some(lst) == succ(count_some(tl));
       assert length(tl) + 1 == length(lst);
       assert succ(nat_of_int(length(tl))) == succ(count_some(tl));
       count_some_forall(tl);
     }
   }
 }
  
 fixpoint int stripe(int start, int step, nat n, int capa) {
   switch(n) {
     case zero: return start;
     case succ(m): return (stripe(start, step, m, capa) + step) % capa;
   }
 }
 
 fixpoint bool list_contains_stripes_helper(list<option<nat> > lst, int start, int step, int index, option<nat> content) {
    switch(content){
     case none: return true;
     case some(n): return stripe(start, step, n, length(lst)) == index;
   }
 }
 
 fixpoint bool list_contains_stripes(list<option<nat> > lst, int start, int step, int index) {
   return list_contains_stripes_helper(lst, start, step, index, nth(index, lst));
 }
 
 lemma void stripe_less_than_capa(int start, int step, nat n, int capa)
 requires start < capa &*& start >= 0 &*& step >= 0;
 ensures stripe(start, step, n, capa) >= 0 &*& stripe(start, step, n, capa) < capa;
 {
   switch(n) {
     case zero: 
     case succ(m): {
       stripe_less_than_capa(start, step, m, capa);
       div_mod_gt_0(stripe(start, step, n, capa), stripe(start, step, m, capa) + step, capa);
     }
   }
 }
 
 lemma void list_none_less_than_n(list<option<nat> > lst, nat n, nat bound)
 requires true == forall(lst, (opt_less_than_n)(n)) &*& int_of_nat(bound) <= length(lst);
 ensures true == up_to(bound, (lst_opt_less_than_n)(lst, n));
 {
   switch(bound){
     case zero: 
     case succ(p_bound): {
       list_none_less_than_n(lst, n, p_bound);
       switch(nth(int_of_nat(p_bound), lst)) {
         case none: 
         case some(val): {
           forall_nth(lst, (opt_less_than_n)(n), int_of_nat(p_bound));
         }
       }
     }
   }
 }
 
 lemma void list_none_contains_stripes(list<option<nat> > lst, int start, int step, nat u_bound)
 requires true == forall(lst, is_none) &*& int_of_nat(u_bound) <= length(lst);
 ensures true == up_to(u_bound, (list_contains_stripes)(lst, start, step));
 {
   switch(u_bound) {
     case zero: {}
     case succ(u_bound_p): {
       list_none_contains_stripes(lst, start, step, u_bound_p);
       switch(nth(int_of_nat(u_bound_p), lst)) {
         case none: {
           assert true == list_contains_stripes(lst, start, step, int_of_nat(u_bound_p));
           assert true == up_to(u_bound_p, (list_contains_stripes)(lst, start, step));
           assert true == up_to(u_bound, (list_contains_stripes)(lst, start, step));
         }
         case some(a): {
           forall_nth(lst, is_none, int_of_nat(u_bound_p));
         }
       }
     }
   }
 }
 
 lemma void count_some_incr(list<option<nat> > lst, int index_update, nat new_val, nat sum)
 requires count_some(lst) == sum &*& nth(index_update, lst) == none &*& index_update < length(lst) &*& index_update >= 0;
 ensures count_some(update(index_update, some(new_val), lst)) == succ(sum);
 {
   switch(lst) {
     case nil: 
     case cons(hd, tl): {
     nat prev_sum;
       switch(hd) {
         case none: prev_sum = sum;
         case some(m): {
           switch(sum) {
             case zero: assert false;
             case succ(p_sum): prev_sum = p_sum;
           }
         }
       }
       
       if(index_update == 0){
       } else {
         count_some_incr(tl, index_update - 1, new_val, prev_sum);
       }
     }
   }
 }
 
 lemma void updated_list_contains_stripes(list<option<nat> > lst, int start, int step, nat n, nat bound)
 requires true == up_to(bound, (list_contains_stripes)(lst, start, step)) &*& int_of_nat(bound) <= length(lst) &*& start >= 0 &*& start < length(lst) &*& step >= 0;
 ensures true == up_to(bound, (list_contains_stripes)(update(stripe(start, step, n, length(lst)), some(n), lst), start, step));
 {
   switch(bound) {
     case zero: 
     case succ(p_bound): {
       updated_list_contains_stripes(lst, start, step, n, p_bound);
       if(stripe(start, step, n, length(lst)) == int_of_nat(p_bound)) {
         nth_update(int_of_nat(p_bound), stripe(start, step, n, length(lst)), some(n), lst);
       } else {
         stripe_less_than_capa(start, step, n, length(lst));
         nth_update(int_of_nat(p_bound), stripe(start, step, n, length(lst)), some(n), lst);         
         switch(nth(int_of_nat(p_bound), lst)){
           case none: 
           case some(content):            
         }
       }
     }
   }
 }
 
 lemma void updated_list_less_than_n(list<option<nat> > lst, int start, int step, nat m, nat bound)
 requires true == up_to(bound, (lst_opt_less_than_n)(lst, m)) &*& int_of_nat(bound) <= length(lst) &*& start >= 0 &*& start < length(lst) &*& step >= 0;
 ensures true == up_to(bound, (lst_opt_less_than_n)(update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst), succ(m)));
 {
   switch(bound) {
     case zero: 
     case succ(p_bound): {
       updated_list_less_than_n(lst, start, step, m, p_bound);
       if(stripe(start, step, succ(m), length(lst)) == int_of_nat(p_bound)) {
         nth_update(int_of_nat(p_bound), stripe(start, step, succ(m), length(lst)), some(succ(m)), lst);
       } else {
         stripe_less_than_capa(start, step, succ(m), length(lst));
         nth_update(int_of_nat(p_bound), stripe(start, step, succ(m), length(lst)), some(succ(m)), lst);
         switch(nth(int_of_nat(p_bound), lst)) {
           case none: 
           case some(content):
         }
       }
     }
   }
 }
 
 lemma void updated_list_not_zero_up_to(list<option<nat> > lst, int start, int step, nat m, nat bound)
 requires true == up_to(bound, (forall_fp_to_up_to_fp)(opt_not_zero, lst)) &*& int_of_nat(bound) <= length(lst) &*& start >= 0 &*& start < length(lst) &*& step >= 0;
 ensures true == up_to(bound, (forall_fp_to_up_to_fp)(opt_not_zero, update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst)));
 {
   switch(bound) {
     case zero:
     case succ(p_bound): {
       updated_list_not_zero_up_to(lst, start, step, m, p_bound);
       option<nat> content_at_pbound = nth(int_of_nat(p_bound), update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst));
       
       if(stripe(start, step, succ(m), length(lst)) == int_of_nat(p_bound)) {
         nth_update(int_of_nat(p_bound), stripe(start, step, succ(m), length(lst)), some(succ(m)), lst);
         assert content_at_pbound == some(succ(m));
         assert true == opt_not_zero(nth(int_of_nat(p_bound), update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst)));
       } else {
         stripe_less_than_capa(start, step, succ(m), length(lst));
         nth_update(int_of_nat(p_bound), stripe(start, step, succ(m), length(lst)), some(succ(m)), lst);
         assert content_at_pbound == nth(int_of_nat(p_bound), lst);
       }
       
       assert true == up_to(bound, (forall_fp_to_up_to_fp)(opt_not_zero, update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst)));
     }
   }
 }

 lemma void updated_list_not_zero_forall(list<option<nat> > lst, int start, int step, nat m)
 requires true == forall(lst, opt_not_zero) &*& start >= 0 &*& start < length(lst) &*& step >= 0;
 ensures true == forall(update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst), opt_not_zero);
 {
   list<option<nat> > new_lst = update(stripe(start, step, succ(m), length(lst)), some(succ(m)), lst);
   
   forall_to_up_to_length(lst, lst, opt_not_zero);
   
   updated_list_not_zero_up_to(lst, start, step, m, nat_of_int(length(lst)));
   
   up_to_length_to_forall(new_lst, 0, new_lst, opt_not_zero);
 }
 
 lemma void stripe_to_arith(int start, int step, nat n, int capa)
 requires start < capa &*& start >= 0 &*& step >= 0;
 ensures stripe(start, step, n, capa) == (start + int_of_nat(n)*step)%capa;
 {
   switch(n) {
     case zero: {
       assert stripe(start, step, zero, capa) == start;
       division_round_to_zero(start, capa);
       div_rem(start, capa);
       assert start == (start + 0*step)%capa;
     }
     case succ(p_n): {
       stripe_to_arith(start, step, p_n, capa);
       assert stripe(start, step, p_n, capa) == (start+int_of_nat(p_n)*step)%capa;
       assert stripe(start, step, n, capa) == ((start + int_of_nat(p_n)*step)%capa + step)%capa;
       assert start >= 0;
       mul_nonnegative(int_of_nat(p_n), step);
       mod_add(start + int_of_nat(p_n)*step, step, capa);
       assert stripe(start, step, n, capa) == (start + int_of_nat(p_n)*step + step) % capa;
       assert stripe(start, step, n, capa) == (start + (int_of_nat(p_n) + 1) * step) % capa;
       assert int_of_nat(p_n)+1 == int_of_nat(succ(p_n));
       mul_subst(int_of_nat(p_n) + 1, int_of_nat(n), step);
       assert stripe(start, step, n, capa) == (start + int_of_nat(n)*step) % capa;
     }
   }
 }

 lemma void mod_eq_sub(int a, int b, int mod, int incr)
 requires true == ((a+incr)%mod == (b+incr)%mod) &*& a >= 0 &*& b >= 0 &*& incr >= 0 &*& incr < mod &*& a < mod &*& b < mod;
 ensures true == (a%mod == b%mod);
 {
   int i = incr;
   for(; i > 0; i--)
   invariant true == ((a+i)%mod == (b+i)%mod) &*& i >= 0;
   decreases i;
   {
     mod_pred_eq(a+i-1, b+i-1, mod);
   }
   assert i == 0;
 }
 
 lemma void CRT_pred(int length_lst, int step, int diff, int start) 
 requires stripe(start, step, zero, length_lst) == stripe(start, step, nat_of_int(diff), length_lst) 
 	&*& diff >= 0 
 	&*& step >= 0 
 	&*& start < length_lst 
 	&*& start >= 0;
 ensures 0 == (diff*step)%length_lst;
 {
   stripe_to_arith(start, step, zero, length_lst);
   stripe_to_arith(start, step, nat_of_int(diff), length_lst);
   mul_subst(int_of_nat(nat_of_int(diff)), diff, step);
   mul_subst(int_of_nat(zero), 0, step);
   
   assert stripe(start, step, zero, length_lst) == start;
   division_round_to_zero(start, length_lst);
   div_rem(start, length_lst);
   assert start == start%length_lst;
   assert start == start + int_of_nat(zero)*step;
   assert stripe(start, step, zero, length_lst) == (start + int_of_nat(zero)*step)%length_lst;
   assert true == ((start + (0*step))%length_lst == (start + diff*step)%length_lst);
   assert 0*step == 0;
   division_round_to_zero(0, length_lst);
   div_rem(0, length_lst);
   
   mul_nonnegative(diff, step);
   assert start == (start + diff*step)%length_lst;
   mod_add(diff*step, start, length_lst);
   assert true == ((start + diff*step)%length_lst == (start + (diff*step)%length_lst)%length_lst);
   div_rem(diff*step, length_lst);
   assert true == ((diff*step)%length_lst < length_lst);
   mod_eq_sub(0, (diff*step)%length_lst, length_lst, start);
   assert 0%length_lst == ((diff*step)%length_lst)%length_lst;
   mod_add(diff*step, 0, length_lst);
 }
 
 lemma void decrease_one_step_stripe(int start, int step, nat val1, nat val2, int capa)
 requires stripe(start, step, succ(val1), capa) == stripe(start, step, succ(val2), capa) &*& int_of_nat(val1) < int_of_nat(val2) &*& capa > 0 &*& step < capa &*& step > 0 &*& start < capa &*& start >= 0;
 ensures stripe(start, step, val1, capa) == stripe(start, step, val2, capa);
 {
   assert stripe(start, step, succ(val1), capa) == (stripe(start, step, val1, capa) + step) % capa;
   assert stripe(start, step, succ(val2), capa) == (stripe(start, step, val2, capa) + step) % capa;
   
   stripe_less_than_capa(start, step, val1, capa);
   stripe_less_than_capa(start, step, val2, capa);
   
   mod_eq_sub(stripe(start, step, val1, capa), stripe(start, step, val2, capa), capa, step);
   
   division_round_to_zero(stripe(start, step, val1, capa), capa);
   div_rem(stripe(start, step, val1, capa), capa);
   
   division_round_to_zero(stripe(start, step, val2, capa), capa);
   div_rem(stripe(start, step, val2, capa), capa);
   
 }
 
 lemma void decrease_stripe(int start, int step, nat val1, nat val2, int capa, int diff)
 requires stripe(start, step, val1, capa) == stripe(start, step, val2, capa) &*& int_of_nat(val2) == int_of_nat(val1) + diff &*& diff > 0 &*& capa > 0 &*& step < capa &*& step > 0 &*& start < capa &*& start >= 0;
 ensures stripe(start, step, zero, capa) == stripe(start, step, nat_of_int(diff), capa);
 {
   switch(val1) {
     case zero: assert val2 == nat_of_int(diff);
     case succ(p_val1): {
       assert val2 == succ(?p_val2);
       decrease_one_step_stripe(start, step, p_val1, p_val2, capa);
       decrease_stripe(start, step, p_val1, p_val2, capa, diff);
     }
   }
 }
 
 lemma void mul_distrib(int a, int b)
 requires true;
 ensures a*b + b == (a+1)*b;
 {
 }

 lemma void decrease_mod_0(nat a, int b)
 requires b > 0;
 ensures 0 == (int_of_nat(a)*b)%b;
 {
   switch(a){
     case zero: div_rem(int_of_nat(a), b); 
     case succ(p_a): {
       decrease_mod_0(p_a, b);
       mul_nonnegative(int_of_nat(p_a), b);
       mod_rotate(int_of_nat(p_a)*b, b);
       
       mul_distrib(int_of_nat(p_a), b);
       succ_int(int_of_nat(p_a));
       assert int_of_nat(p_a)*b + b == (int_of_nat(p_a) + 1) * b;
       mul_subst(int_of_nat(a), int_of_nat(p_a) + 1, b);
       assert int_of_nat(a) == int_of_nat(p_a) + 1;
       assert int_of_nat(p_a) * b + b == int_of_nat(a) * b;
     }
   }
 }
 
 fixpoint list<option<nat> > stripe_l_fp(int start, int step, nat n, int capa)
 {
   switch(n) {
     case zero: return gen_none(nat_of_int(capa));
     case succ(m): return update(stripe(start, step, n, capa), some(n), stripe_l_fp(start, step, m, capa));
   }
 }
 
 lemma list<option<nat> > stripe_l(int start, int step, nat n, int capa)
 requires 0 <= start &*& start < capa &*& step > 0 &*& int_of_nat(n) <= capa &*& coprime(step, capa) &*& step < capa;
 ensures count_some(result) == n
 	&*& length(result) == capa
 	&*& true == up_to(nat_of_int(capa), (list_contains_stripes)(result, start, step))
 	&*& true == up_to(nat_of_int(capa), (lst_opt_less_than_n)(result, n))
 	&*& true == forall(result, opt_not_zero)
 	&*& result == stripe_l_fp(start, step, n, capa)
 	&*& coprime(step, capa);
 {
   switch(n) {
     case zero: {
       list<option<nat> > lst = gen_none(nat_of_int(capa));
       gen_none_l(nat_of_int(capa));
       list_none_contains_stripes(lst, start, step, nat_of_int(length(lst)));
       gen_none_less_than(nat_of_int(capa), n);
       list_none_less_than_n(lst, zero, nat_of_int(capa));
       return lst;
     }
     case succ(m): {
       list<option<nat> > lst = stripe_l(start, step, m, capa);
       assert true == forall(lst, opt_not_zero);
       assert count_some(lst) == m;
       switch(nth(stripe(start, step, n, capa), lst))
       {
         case some(prev_val): {
           int index = stripe(start, step, n, capa);
           stripe_less_than_capa(start, step, n, capa);
           forall_nth(lst, opt_not_zero, stripe(start, step, n, capa));
           assert prev_val != zero;
           int diff = int_of_nat(n) - int_of_nat(prev_val);
           up_to_covers_x(nat_of_int(length(lst)), (lst_opt_less_than_n)(lst, m), index);
           assert diff >= 0;
           up_to_covers_x(nat_of_int(length(lst)), (list_contains_stripes)(lst, start, step), index);
           
           assert true == list_contains_stripes(lst, start, step, index);
           assert stripe(start, step, prev_val, capa) == stripe(start, step, n, capa);
           decrease_stripe(start, step, prev_val, n, capa, diff);
           
           CRT_pred(length(lst), step, diff, start);
           assert 0 == (diff*step)%length(lst) &*& diff < length(lst);
           
           // from CRT
           decrease_mod_0(nat_of_int(diff), step);
           assert diff == int_of_nat(nat_of_int(diff));
           mul_subst(diff, int_of_nat(nat_of_int(diff)), step);
           assert 0 == (diff*step)%step;
           decrease_mod_0(nat_of_int(diff), step);
           mul_mono_strict(diff, capa, step);
           bin_chinese_remainder_theorem(step, capa, diff*step);
           assert diff > 0;
           assert step > 0;
           mul_positive(diff, step);
           assert false;
         }
         
         case none:
       }
       list<option<nat> > new_lst = update(stripe(start, step, n, capa), some(n), lst); // Get a new list 
       stripe_less_than_capa(start, step, n, capa);
       count_some_incr(lst, stripe(start, step, n, capa), n, m);
       updated_list_contains_stripes(lst, start, step, n, nat_of_int(capa));
       updated_list_less_than_n(lst, start, step, m, nat_of_int(capa));
       updated_list_not_zero_forall(lst, start, step, m);
       return new_lst;
     }
   }
 }
 
 lemma void nat_diff_int_diff(nat n1, nat n2)
 requires n1 != n2;
 ensures int_of_nat(n1) != int_of_nat(n2);
 {
   switch(n1){
     case zero:
     case succ(p1): {
       switch(n2) {
         case zero:
         case succ(p2): nat_diff_int_diff(p1, p2);
       }
     }
   }
 }
 
 lemma void up_to_weak(nat bound, nat new_bound, fixpoint(int, bool) prop)
 requires true == up_to(bound, prop) &*& int_of_nat(new_bound) <= int_of_nat(bound);
 ensures true == up_to(new_bound, prop);
 {
   switch(bound){
     case zero: assert new_bound == zero;
     case succ(p_bound): {
       if(new_bound == bound){
       } else {
         nat_diff_int_diff(bound, new_bound);
         assert int_of_nat(bound) != int_of_nat(new_bound);
         up_to_weak(p_bound, new_bound, prop);
       }
     }
   }
 }
 
 lemma void loop_fp_pos(int k, int capacity)
 requires k >= 0 &*& capacity > 0;
 ensures loop_fp(k, capacity) == k%capacity;
 {
   mod_rotate(k, capacity);
   assert true == ((k+capacity)%capacity == k%capacity);
   assert loop_fp(k, capacity) == (k%capacity + capacity)%capacity;
   mod_add(k, capacity, capacity);
   assert loop_fp(k, capacity) == (k+capacity)%capacity;
   
 }
 
 // if a cell is some in stripe_l_fp, and strideNthProp hold up to an higher bound, then prop holds for that cell
 lemma void stride_to_stripe<t>(int start, int step, nat bound_stripe, nat bound_stride, int capa, int n, fixpoint(t, bool) prop, list<t> lst)
 requires true == up_to(bound_stride, (stride_nth_prop)(lst, prop, capa, start, step)) 
 	&*& int_of_nat(bound_stripe) < int_of_nat(bound_stride) 
 	&*& 0 <= n &*& n < capa &*& 0 <= start &*& start < capa &*& step > 0 &*& int_of_nat(bound_stripe) <= capa &*& coprime(step, capa) &*& step < capa;
 ensures coprime(step, capa) 
 	&*& true == (true == is_some(nth(n, stripe_l_fp(start, step, bound_stripe, capa))) ? nthProp(lst, prop, n) : true);
 {
   switch(bound_stripe) {
     case zero: {
       // Prove all none;
       list<option<nat> > lst_none = stripe_l(start, step, bound_stripe, capa);
       assert lst_none == gen_none(nat_of_int(capa));
       gen_none_l(nat_of_int(capa));
       assert length(lst_none) == capa;
       assert n < capa;
       assert int_of_nat(nat_of_int(n)) == n;
       forall_fp_to_fp(lst_none, is_none, nat_of_int(n));
       assert false == is_some(nth(n, stripe_l_fp(start, step, bound_stripe, capa)));
     }
     case succ(p_bound_stripe): {
       list<option<nat> > lst_stripe = stripe_l(start, step, bound_stripe, capa);  
       switch(nth(n, stripe_l_fp(start, step, bound_stripe, capa))) {
         case none: assert false == is_some(nth(n, stripe_l_fp(start, step, bound_stripe, capa)));
         case some(n_s): {
           int nb_steps = int_of_nat(n_s);
           assert true == up_to(nat_of_int(capa), (lst_opt_less_than_n)(lst_stripe, bound_stripe));
           up_to_weak(nat_of_int(capa), succ(nat_of_int(n)), (lst_opt_less_than_n)(lst_stripe, bound_stripe));
           assert lst_opt_less_than_n(lst_stripe, bound_stripe, n) == true;
           assert nb_steps <= int_of_nat(bound_stripe) &*& int_of_nat(bound_stripe) <= int_of_nat(bound_stride);
           
           up_to_weak(nat_of_int(capa), succ(nat_of_int(n)), (list_contains_stripes)(lst_stripe, start, step));
           stripe_to_arith(start, step, n_s, capa);
           assert n == (start + step*nb_steps) % capa;
           
           up_to_weak(bound_stride, succ(n_s), (stride_nth_prop)(lst, prop, capa, start, step));
           assert stride_nth_prop(lst, prop, capa, start, step, nb_steps) == true;
           
           
           assert true == nthProp(lst, prop, loop_fp(start + step*nb_steps, capa));
           
           mul_nonnegative(step, nb_steps);
           loop_fp_pos(start + step * nb_steps, capa);
           assert loop_fp(start + step * nb_steps, capa) == (start + step*nb_steps)%capa;
         }
       }
     }
   }
 }

 lemma void apply_CRT<t>(int i, list<t> ts, fixpoint (t, bool) prop, int capacity, int start, int offset)
 requires true == up_to(nat_of_int(i),(stride_nth_prop)(ts, prop, capacity, start, offset))
 	&*& coprime(offset, capacity)
 	&*& i > capacity
 	&*& capacity >= 0 &*& 0 <= start &*& start < capacity &*& offset > 0 &*& offset < capacity
 	&*& length(ts) == capacity;
 ensures true == up_to(nat_of_int(length(ts)), (nthProp)(ts, prop)) &*& coprime(offset, capacity); 
 {
   nat bound = nat_of_int(capacity);
   up_to_weak(nat_of_int(i), succ(bound), (stride_nth_prop)(ts, prop, capacity, start, offset));
   // Proof steps: 
   // Show that stripe_l(..., n == capa, ...) => forall(is_some, stripe_l)
   list<option<nat> > lst_stripe = stripe_l(start, offset, bound, capacity);
   assert count_some(lst_stripe) == bound;
   count_some_forall(lst_stripe);
   assert true == forall(lst_stripe, is_some);
   
   // Show that if up_to(bound, stride_nth_prop(prop,...)), then stride_nth_prop(prop,...,index) iff is_some(nth(index, stripe_l(...)));
   int iter = 0;
   for(; iter < length(ts); iter++)
   invariant true == up_to(nat_of_int(iter), (nthProp)(ts, prop))
   	&*& iter <= length(ts)
   	&*& iter >= 0
   	&*& coprime(offset, capacity)
   	&*& true == forall(lst_stripe, is_some);
   decreases length(ts) - iter;
   {
     forall_fp_to_fp(stripe_l_fp(start, offset, bound, capacity), is_some, nat_of_int(iter));
     assert is_some(nth(iter, stripe_l_fp(start, offset, bound, capacity))) == true;
     stride_to_stripe(start, offset, bound, succ(bound), capacity, iter, prop, ts);
     assert nthProp(ts, prop, iter) == true;
     assert true == up_to(nat_of_int(iter), (nthProp)(ts, prop));
     assert true == up_to(succ(nat_of_int(iter)), (nthProp)(ts, prop));
   }
   // Hence, if exists( !prop) => !forall(is_some, stripe_l) => false
 }
@*/

static
int hash_equal(entry_t h1, entry_t h2)
  //@ requires true;
  //@ ensures h1 == h2 ? (result != 0) : result == 0;
{
  if(h1 == h2) {
  	return 1;
  } else {
  	return 0;
  }
}

static
unsigned int loop(unsigned int entry_point, unsigned int capacity)
//@ requires 0 < capacity &*& 2*capacity < INT_MAX;
/*@ ensures 0 <= result &*& result < capacity &*&
            result == loop_fp(entry_point, capacity); @*/
{
  unsigned int g = entry_point%capacity;
  //@ div_mod(g, entry_point, capacity);
  //@ assert(2*capacity< INT_MAX);
  unsigned int res = (g + capacity)%capacity;
  //@ div_mod_gt_0(res, g + capacity, capacity);
  //@ assert (res < capacity);
  //@ int s_res = (int) res;
  //@ assert (res == s_res);
  return res;
}

/*@
  inductive hmap<kt> = hmap(list<option<kt> >, list<int>);

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash_entry,
                         fixpoint (kt, int) hash_offset,
                         int capacity,
                         int* busybits,
                         list<void*> kps,
                         entry_t* k_hashes;
                         hmap<kt> m);

  fixpoint list<option<kt> > hmap_ks_fp<kt>(hmap<kt> m) {
    switch(m) { case hmap(ks, khs): return ks; }
  }

  fixpoint int ks_size_fp<kt>(list<option<kt> > ks) {
    switch(ks) {
      case nil: return 0;
      case cons(h,t): return (h == none ? 0 : 1) + ks_size_fp(t);
    }
  }

  fixpoint int hmap_size_fp<kt>(hmap<kt> m) {
    return ks_size_fp(hmap_ks_fp(m));
  }

  fixpoint bool hmap_empty_cell_fp<kt>(hmap<kt> m, int index) {
    return (nth(index, hmap_ks_fp(m)) == none);
  }

  fixpoint bool hmap_exists_key_fp<kt>(hmap<kt> m, kt k) {
    return mem(some(k), hmap_ks_fp(m));
  }

  fixpoint int hmap_find_key_fp<kt>(hmap<kt> m, kt k) {
    return index_of(some(k), hmap_ks_fp(m));
  }

  fixpoint hmap<kt> hmap_put_key_fp<kt>(hmap<kt> m, int i, kt k, int hash) {
    switch(m) { case hmap(ks, khs):
      return hmap(update(i, some(k), ks), update(i, hash, khs));
    }
  }

  fixpoint hmap<kt> hmap_rem_key_fp<kt>(hmap<kt> m, int i) {
    switch(m) { case hmap(ks, khs):
      return hmap(update(i, none, ks), khs);
    }
  }

  @*/

/*@

  predicate pred_mapping<t>(list<void*> pts, list<int> bbs,
                            predicate (void*; t) pred;
                            list<option<t> > ks) =
            bbs == nil ? (ks == nil &*& pts == nil) :
              (pred_mapping(tail(pts), tail(bbs), pred, ?kst) &*&
               pts != nil &*&
               (head(bbs) == 0 ? ks == cons(none, kst) :
                 ([0.5]pred(head(pts), ?ksh) &*& ks == cons(some(ksh), kst))));

  fixpoint bool no_dups<t>(list<option<t> > l) {
    switch(l) {
      case nil: return true;
      case cons(h,t):
        return no_dups(t) && (h == none || !(mem(h, t)));
    }
  }

  fixpoint bool hash_list<kt>(list<option<kt> > vals,
                             list<int> hashes,
                             fixpoint (kt, int) hash) {
    switch(vals) {
      case nil: return hashes == nil;
      case cons(h,t):
        return hash_list(t, tail(hashes), hash) &&
               hashes != nil &&
               (h == none || head(hashes) == hash(get_some(h)));
    }
  }

  predicate hmapping<kt>(predicate (void*; kt) keyp,
                         fixpoint (kt, int) hash_entry,
                         fixpoint (kt, int) hash_offset,
                         int capacity,
                         int* busybits,
                         list<void*> kps,
                         entry_t* k_hashes;
                         hmap<kt> m) =
            0 < capacity &*& 2*capacity < INT_MAX &*&
            ints(busybits, capacity, ?bbs) &*&
            uints(k_hashes, capacity, ?khs) &*&
            pred_mapping(kps, bbs, keyp, ?ks) &*&
            true == no_dups(ks) &*&
            true == hash_list(ks, khs, hash_entry) &*&
            m == hmap(ks, khs);
@*/
/*@
  lemma void pred_mapping_same_len<t>(list<int> bbs, list<option<t> > ks)
  requires pred_mapping(?pts, bbs, ?pred, ks);
  ensures pred_mapping(pts, bbs, pred, ks) &*&
          length(bbs) == length(ks);
  {
    open pred_mapping(_, _, _, _);
    switch(bbs) {
      case nil:
        assert(ks == nil);
        break;
      case cons(h, t):
        pred_mapping_same_len(t, tail(ks));
    }
    close pred_mapping(pts, bbs, pred, ks);
  }

  lemma kt extract_pred_for_key<kt>(list<void*> kps_b,
                                    list<int> bbs_b,
                                    list<option<kt> > ks_b,
                                    int n, list<int> bbs,
                                    list<option<kt> > ks)
  requires pred_mapping(?kps, bbs, ?pred, ks) &*&
           pred_mapping(kps_b, bbs_b, pred, ks_b) &*&
           0 <= n &*& n < length(bbs) &*& nth(n, bbs) != 0;
  ensures nth(n, ks) == some(result) &*& [0.5]pred(nth(n, kps), result) &*&
          pred_mapping(drop(n+1, kps), drop(n+1, bbs), pred, drop(n+1, ks)) &*&
          pred_mapping(append(reverse(take(n, kps)), kps_b),
                       append(reverse(take(n, bbs)), bbs_b),
                       pred,
                       append(reverse(take(n, ks)), ks_b));
  {
    open pred_mapping(kps, _, _, _);
    switch(bbs) {
      case nil:
        assert(length(bbs) == 0);
        return default_value<kt>();
      case cons(bbh, bbt):
        switch(kps) {
          case nil: return default_value<kt>();
          case cons(kph, kpt):
            switch(ks) {
              case nil: return default_value<kt>();
              case cons(kh, kt) :
              if (n == 0) {
                switch(kh) {
                  case some(k):
                    return k;
                  case none: return default_value<kt>();
                }
              } else {
                append_reverse_take_cons(n,kph,kpt,kps_b);
                append_reverse_take_cons(n,bbh,bbt,bbs_b);
                append_reverse_take_cons(n,kh,kt,ks_b);
                return extract_pred_for_key(cons(kph,kps_b),
                                            cons(bbh,bbs_b),
                                            cons(kh, ks_b),
                                            n-1, bbt, kt);
              }
            }
        }
    }
  }

  lemma void reconstruct_pred_mapping<kt>(list<void*> kps1,
                                          list<int> bbs1,
                                          list<option<kt> > ks1,
                                          list<void*> kps2,
                                          list<int> bbs2,
                                          list<option<kt> > ks2)
  requires pred_mapping(kps1, bbs1, ?pred, ks1) &*&
           pred_mapping(kps2, bbs2, pred, ks2);
  ensures pred_mapping(append(reverse(kps1), kps2),
                       append(reverse(bbs1), bbs2),
                       pred,
                       append(reverse(ks1), ks2));
  {
    open pred_mapping(kps1, bbs1, pred, ks1);
    switch(bbs1) {
      case nil:
        assert(kps1 == nil);
        assert(ks1 == nil);
        return;
      case cons(bbh, bbt):
        append_reverse_tail_cons_head(kps1, kps2);
        append_reverse_tail_cons_head(bbs1, bbs2);
        append_reverse_tail_cons_head(ks1, ks2);
        reconstruct_pred_mapping(tail(kps1), bbt, tail(ks1),
                                 cons(head(kps1), kps2),
                                 cons(bbh, bbs2),
                                 cons(head(ks1), ks2));
    }
  }

  lemma void recover_pred_mapping<kt>(list<void*> kps, list<int> bbs,
                                      list<option<kt> > ks,
                                      int n)
  requires pred_mapping(reverse(take(n, kps)), reverse(take(n, bbs)),
                        ?pred, reverse(take(n, ks))) &*&
           nth(n, bbs) != 0 &*&
           [0.5]pred(nth(n, kps), ?k) &*&
           nth(n, ks) == some(k) &*&
           pred_mapping(drop(n+1, kps), drop(n+1, bbs),
                        pred, drop(n+1, ks)) &*&
           0 <= n &*& n < length(kps) &*&
           n < length(bbs) &*&
           n < length(ks);
  ensures pred_mapping(kps, bbs, pred, ks);
  {
    close pred_mapping(cons(nth(n, kps), drop(n+1,kps)),
                       cons(nth(n, bbs), drop(n+1,bbs)),
                       pred,
                       cons(nth(n, ks), drop(n+1, ks)));
    drop_n_plus_one(n, kps);
    drop_n_plus_one(n, bbs);
    drop_n_plus_one(n, ks);
    reconstruct_pred_mapping(reverse(take(n, kps)),
                             reverse(take(n, bbs)),
                             reverse(take(n, ks)),
                             drop(n, kps),
                             drop(n, bbs),
                             drop(n, ks));
  }

  lemma void no_dups_same<kt>(list<option<kt> > ks, kt k, int n, int m)
  requires true == no_dups(ks) &*& 0 <= n &*& n < length(ks) &*&
           0 <= m &*& m < length(ks) &*&
           nth(n, ks) == some(k) &*& nth(m, ks) == some(k);
  ensures n == m;
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        if (n == 0) {
          assert(h == some(k));
          assert(!mem(h, t));
        } else if (m == 0) {
        } else {
          assert(0<n);
          assert(0<m);
          no_dups_same(t, k, n-1, m-1);
        }
    }
  }

  lemma void ks_find_this_key<kt>(list<option<kt> > ks, int i, kt k)
  requires nth(i, ks) == some(k) &*& true == no_dups(ks) &*&
           0 <= i &*& i < length(ks);
  ensures index_of(some(k), ks) == i;
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        if (h == some(k)) {
          no_dups_same(ks, k, i, 0);
          assert(i == 0);
          return;
        } else {
          ks_find_this_key(t, i-1, k);
        }
    }
  }

  lemma void hmap_find_this_key<kt>(hmap<kt> m, int i, kt k)
  requires nth(i, hmap_ks_fp(m)) == some(k) &*& true == no_dups(hmap_ks_fp(m)) &*&
           0 <= i &*& i < length(hmap_ks_fp(m));
  ensures hmap_find_key_fp(m, k) == i;
  {
    ks_find_this_key(hmap_ks_fp(m), i, k);
  }

  fixpoint bool not_my_key<kt>(kt k, option<kt> arg) {
    return arg != some(k);
  }

  lemma void no_hash_no_key<kt>(list<option<kt> > ks, list<int> hashes,
                                kt k, int i, fixpoint (kt,int) hash)
  requires true == hash_list(ks, hashes, hash) &*&
           nth(i, hashes) != hash(k) &*&
           0 <= i &*& i < length(ks);
  ensures nth(i, ks) != some(k);
  {
    switch(ks) {
      case nil:
        assert(hashes == nil);
        return;
      case cons(kh,kt):
        assert(hashes != nil);
        if (i == 0) {
          assert(nth(i, ks) == kh);
          if (kh == some(k)) {
            assert(head(hashes) == hash(k));
            nth_0_head(hashes);
            assert(nth(i, hashes) == head(hashes));
            assert(nth(i, hashes) == hash(k));
          }
          return;
        } else {
          nth_cons(i, tail(hashes), head(hashes));
          cons_head_tail(hashes);
          assert(nth(i, hashes) == nth(i-1,tail(hashes)));
          no_hash_no_key(kt, tail(hashes), k, i-1, hash);
        }
    }
  }
@*/

/*@
  lemma void no_bb_no_key<kt>(list<option<kt> > ks, list<int> bbs, int i)
  requires pred_mapping(?kps, bbs, ?pred, ks) &*& 0 <= i &*& i < length(ks) &*&
           nth(i, bbs) == 0;
  ensures pred_mapping(kps, bbs, pred, ks) &*& nth(i, ks) == none;
  {
    open pred_mapping(kps, bbs, pred, ks);
    switch(bbs) {
      case nil: ;
      case cons(bbh,bbt):
        if (i == 0) {
          nth_0_head(bbs);
          nth_0_head(ks);
        } else {
          no_bb_no_key(tail(ks), tail(bbs), i-1);
        }
    }
    close pred_mapping(kps, bbs, pred, ks);
  }
@*/

/*@

  lemma void up_to_nth_uncons<kt>(kt hd, list<kt> tl, fixpoint (kt, bool) prop)
  requires true == up_to(succ(nat_of_int(length(tl))),
                         (nthProp)(cons(hd,tl), prop));
  ensures true == up_to(nat_of_int(length(tl)), (nthProp)(tl, prop)) &*&
          true == prop(hd);
  {
    shift_for_all(cons(hd,tl), prop, 1, length(tl)+1, nat_of_int(length(tl)));
    shift_for_append(cons(hd,nil), tl, prop, nat_of_int(length(tl)));
    up_to_covers_x(nat_of_int(length(tl)+1), (nthProp)(cons(hd,tl), prop), 0);
  }

  lemma void no_key_found<kt>(list<option<kt> > ks, kt k)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, (not_my_key)(k)));
  ensures false == mem(some(k), ks);
  {
    switch(ks){
      case nil: return;
      case cons(h,t):
        up_to_nth_uncons(h, t, (not_my_key)(k));
        no_key_found(t, k);
    }
  }
@*/
static
int find_key /*@ <kt> @*/ (int* busybits, void** keyps, entry_t *k_hashes, unsigned int start,
		void* keyp, map_keys_equality* eq, entry_t hash_entry, offset_t hash_offset,
		unsigned int capacity)
/*@ requires hmapping<kt>(?kpr, ?hsh_entry, ?hsh_offset, capacity, busybits, ?kps, k_hashes, ?hm) &*&
             pointers(keyps, capacity, kps) &*&
             [?kfr]kpr(keyp, ?k) &*&
             hsh_entry(k) == hash_entry &*&
             hsh_offset(k) == hash_offset &*&
             0 <= start &*& 2*start < INT_MAX &*&
             [?f]is_map_keys_equality<kt>(eq, kpr) &*&
             coprime(hash_offset, capacity) &*&
             hash_offset > 0 &*& 
             hash_offset < capacity &*&
             start < capacity; @*/
/*@ ensures hmapping<kt>(kpr, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm) &*&
            pointers(keyps, capacity, kps) &*&
            [kfr]kpr(keyp, k) &*&
            [f]is_map_keys_equality<kt>(eq, kpr) &*&
            coprime(hash_offset, capacity) &*&
            (hmap_exists_key_fp(hm, k) ?
            (result == hmap_find_key_fp(hm, k)) :
             (result == -1)); @*/
{
  //@ open hmapping(_, _, _, _, _, _, _, hm);
  //@ assert pred_mapping(kps, ?bbs, kpr, ?ks);
  //@ assert hm == hmap(ks, ?khs);

  int i = 0;
  int capacity_s = (int) capacity;
  offset_t offset = hash_offset;
  unsigned int index = loop(start, capacity);
  //@ mod_add(start, capacity, capacity);
  //@ mod_rotate(start, capacity);
  //@ assert coprime(offset, capacity);
  for (; i < capacity_s + 1; ++i)
    /*@ invariant pred_mapping(kps, bbs, kpr, ks) &*&
                  ints(busybits, capacity, bbs) &*&
                  uints(k_hashes, capacity, khs) &*&
                  pointers(keyps, capacity, kps) &*&
                  0 <= i &*& i <= capacity + 1 &*&
                  [f]is_map_keys_equality<kt>(eq, kpr) &*&
                  [kfr]kpr(keyp, k) &*&
                  hsh_entry(k) == hash_entry &*&
                  hsh_offset(k) == hash_offset &*&
                  true == hash_list(ks, khs, hsh_entry) &*&
                  true == up_to(nat_of_int(i),(stride_nth_prop)(ks, (not_my_key)(k), capacity, start, offset)) &*& 
                  index < capacity &*& offset < capacity &*& 2*capacity < INT_MAX &*& index == (i*offset+start)%capacity&*&
                  start >= 0;
    @*/
    //@ decreases capacity_s - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    //@ assert(sizeof(int) == 4);
    //@ assert(sizeof(long long) == 8);
    //@ assert(sizeof(hash_t) == 8);
    int bb = busybits[(int) index];
    entry_t kh = 0;
    kh = k_hashes[(int) index];
    void* kp = keyps[(int)index];
    int hash_eq = hash_equal(kh, hash_entry);
    if (bb != 0 && hash_eq) {
      //@ assert (nth(index, khs) == hsh_entry(k));
      //@ close pred_mapping(nil, nil, kpr, nil);
      //@ extract_pred_for_key(nil, nil, nil, index, bbs, ks);
      //@ append_nil(reverse(take(index, kps)));
      //@ append_nil(reverse(take(index, bbs)));
      //@ append_nil(reverse(take(index, ks)));
      if (eq(kp, keyp)) {
        /*@ recover_pred_mapping(kps, bbs, ks, index); @*/
        //@ hmap_find_this_key(hm, index, k);
        //@ close hmapping<kt>(kpr, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
        return (int) index;
      }
      //@ recover_pred_mapping(kps, bbs, ks, index);
    } else {
      //@ assert(length(ks) == capacity);
      //@ if (bb == 0) no_bb_no_key(ks, bbs, index);
      /*@ if (bb != 0) {
			assert(nth(index, khs) != hsh_entry(k));
			no_hash_no_key(ks, khs, k, index, hsh_entry);
		} @*/
    }
    //@ assert(nth(index, ks) != some(k));
    //@ assert(true == not_my_key(k, nth(index, ks)));
    //@ assert index == (i*offset+start)%capacity;
    //@ mul_nonnegative(i, offset);
    //@ mod_add(i*offset + start, capacity, capacity);
    //@ mod_rotate(i*offset + start, capacity);
    //@ assert(true == not_my_key(k, nth(loop_fp(i*offset+start,capacity), ks)));
    
    
    index = loop(index + offset, capacity);
    //@ mul_nonnegative(i, offset);
    //@ div_mod_gt_0(((i*offset + start)%capacity + offset)%capacity, (i*offset + start)%capacity + offset, capacity);
    //@ mod_add((i*offset+start)%capacity + offset, capacity, capacity);
    //@ mod_rotate((i*offset+start)%capacity + offset, capacity);
    //@ mod_add(i*offset+start, offset, capacity);
    //@ mul_distrib(i, offset);    
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ assert i == capacity + 1;
  //@ apply_CRT(i, ks, (not_my_key)(k), capacity, start, offset);
  //@ assert true == up_to(nat_of_int(length(ks)), (nthProp)(ks, (not_my_key)(k))); 
  //@ no_key_found(ks, k);
  //@ close hmapping<kt>(kpr, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  return -1;
}

/*@
  lemma void ks_size_limits<kt>(list<option<kt> > ks)
  requires true;
  ensures 0 <= ks_size_fp(ks) &*& ks_size_fp(ks) <= length(ks);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        ks_size_limits(t);
    }
  }

  lemma void zero_bbs_is_for_empty<kt>(list<int> bbs,
                                       list<option<kt> > ks, int i)
  requires pred_mapping(?kps, bbs, ?kpr, ks) &*& nth(i, bbs) == 0 &*&
           0 <= i &*& i < length(bbs);
  ensures pred_mapping(kps, bbs, kpr, ks) &*& nth(i, ks) == none &*&
          ks_size_fp(ks) < length(ks);
  {
    open pred_mapping(kps, bbs, kpr, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
          assert(head(ks) == none);
          ks_size_limits(tail(ks));
        } else {
          nth_cons(i, t, h);
          zero_bbs_is_for_empty(t, tail(ks), i-1);
        }
    }
    close pred_mapping(kps, bbs, kpr, ks);
  }

  fixpoint bool cell_busy<kt>(option<kt> x) { return x != none; }

  lemma void bb_nonzero_cell_busy<kt>(list<int> bbs, list<option<kt> > ks, int i)
  requires pred_mapping(?kps, bbs, ?kp, ks) &*& nth(i, bbs) != 0 &*&
           0 <= i &*& i < length(bbs);
  ensures pred_mapping(kps, bbs, kp, ks) &*& true == cell_busy(nth(i, ks));
  {
    open pred_mapping(kps, bbs, kp, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
      if (i == 0) {
      } else {
        nth_cons(i, t, h);
        bb_nonzero_cell_busy(t, tail(ks), i-1);
      }
    }
    close pred_mapping(kps, bbs, kp, ks);
  }

  lemma void full_size<kt>(list<option<kt> > ks)
  requires true == up_to(nat_of_int(length(ks)), (nthProp)(ks, cell_busy));
  ensures ks_size_fp(ks) == length(ks);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        up_to_nth_uncons(h, t, cell_busy);
        full_size(t);
    }
  }
  @*/
static
int find_empty /*@ <kt> @*/(int* busybits, unsigned int start, entry_t hash_entry, offset_t hash_offset, unsigned int capacity)
  /*@ requires hmapping<kt>(?kp, ?hsh_entry, ?hsh_offset, capacity, busybits, ?kps, ?k_hashes, ?hm) &*&
    pointers(?keyps, capacity, kps) &*&
    0 <= start &*& 2*start < INT_MAX &*&
             coprime(hash_offset, capacity) &*&
             hash_offset > 0 &*& 
             hash_offset < capacity &*&
             start < capacity; @*/
  /*@ ensures hmapping<kt>(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm) &*&
    pointers(keyps, capacity, kps) &*&
    (hmap_size_fp(hm) < capacity ?
    (true == hmap_empty_cell_fp(hm, result) &*&
    0 <= result &*& result < capacity) :
    result == -1) &*& coprime(hash_offset, capacity); @*/
{
  //@ open hmapping(_, _, _, _, _, _, _, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ?ks);
  //@ assert hm == hmap(ks, ?khs);
  int i = 0;
  int capacity_s = (int) capacity;
  offset_t offset = hash_offset;
  for (; i < capacity_s + 1; ++i)
    /*@ invariant pred_mapping(kps, bbs, kp, ks) &*&
      ints(busybits, capacity, bbs) &*&
      uints(k_hashes, capacity, khs) &*&
      pointers(keyps, capacity, kps) &*&
      0 <= i &*& i <= capacity + 1&*&
      true == up_to(nat_of_int(i), (stride_nth_prop)(ks, cell_busy, capacity, start, offset));
      @*/
    //@ decreases capacity_s - i;
  {
    //@ pred_mapping_same_len(bbs, ks);
    unsigned int index = loop(start + ((unsigned int) i)*offset, capacity);
    int bb = busybits[(int)index];
    if (0 == bb) {
      //@ zero_bbs_is_for_empty(bbs, ks, index);
      //@ close hmapping<kt>(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
      return (int)index;
    }
    //@ bb_nonzero_cell_busy(bbs, ks, index);
    //@ assert(true == cell_busy(nth(loop_fp(i*offset+start,capacity), ks)));
    //@ assert(nat_of_int(i+1) == succ(nat_of_int(i)));
  }
  //@ pred_mapping_same_len(bbs, ks);
  //@ apply_CRT(capacity+1, ks, cell_busy, capacity, start, offset);
  //@ full_size(ks);
  //@ close hmapping<kt>(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  return -1;
}

/*@
  fixpoint list<int> zero_list_fp(nat len) {
    switch(len) {
      case zero: return nil;
      case succ(x): return cons(0, zero_list_fp(x));
    }
  }

  fixpoint list<option<kt> > none_list_fp<kt>(nat len) {
    switch(len) {
      case zero: return nil;
      case succ(l): return cons(none,none_list_fp(l));
    }
  }

  lemma void move_int(int* data, int i, int len)
  requires ints(data, i, ?l1) &*& ints(data + i, len - i, ?l2) &*&
           i < len;
  ensures ints(data, i + 1, append(l1,cons(head(l2),nil))) &*&
          ints(data + i + 1, len - i - 1, tail(l2));
  {
    open(ints(data, i, l1));
    switch(l1) {
      case nil:
        open(ints(data, len-i, l2));
        close(ints(data, 1, cons(head(l2),nil)));
      case cons(h,t):
        move_int(data+1, i-1, len-1);
    }
    close(ints(data, i+1, append(l1, cons(head(l2),nil))));
  }

  lemma void extend_zero_list(nat len, int extra)
  requires true;
  ensures update(int_of_nat(len), 0,
                 append(zero_list_fp(len), cons(extra,nil))) ==
          zero_list_fp(succ(len));
  {
    switch(len) {
      case zero: return;
      case succ(l):
        extend_zero_list(l, extra);
    }
  }

  fixpoint hmap<kt> empty_hmap_fp<kt>(int capacity, list<int> hashes) {
    return hmap(none_list_fp<kt>(nat_of_int(capacity)),
                hashes);
  }

  lemma void nat_len_of_non_nil<t>(t h, list<t> t)
  requires true;
  ensures nat_of_int(length(cons(h, t)) - 1) == nat_of_int(length(t)) &*&
          nat_of_int(length(cons(h, t))) == succ(nat_of_int(length(t)));
  {
    int l = length(cons(h,t));
    assert(0 < l);
    switch(nat_of_int(l)) {
      case zero:
        note(int_of_nat(zero) == l);
        assert(false);
        return;
      case succ(lll):
        assert(nat_of_int(l) == succ(lll));
        assert(nat_of_int(int_of_nat(lll) + 1) == succ(nat_of_int(int_of_nat(lll))));
        assert(nat_of_int(int_of_nat(lll) + 1) == nat_of_int(l));
        assert(int_of_nat(nat_of_int(int_of_nat(lll) + 1)) == int_of_nat(nat_of_int(l)));
        assert(int_of_nat(lll) + 1 == l);
        assert(nat_of_int(int_of_nat(lll)) == nat_of_int(l-1));
        assert(lll == nat_of_int(l-1));
        return;
    }
  }

  lemma void produce_pred_mapping<kt>(list<int> hashes,
                                      predicate (void*; kt) kp,
                                      list<void*> pts)
  requires length(hashes) == length(pts);
  ensures pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                       kp, none_list_fp<kt>(nat_of_int(length(pts))));
  {
    switch(pts) {
      case nil:
        close pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                           kp, none_list_fp<kt>(nat_of_int(length(pts))));
        return;
      case cons(pth,ptt):
        switch(hashes) {
          case nil: break;
          case cons(hh,ht): break;
        }
        assert(hashes != nil);
        produce_pred_mapping(tail(hashes), kp, ptt);
        nat_len_of_non_nil(pth,ptt);
        close pred_mapping(pts, zero_list_fp(nat_of_int(length(pts))),
                           kp, none_list_fp<kt>(nat_of_int(length(pts))));
        return;
    }
  }

  lemma void confirm_no_dups_on_nones<kt>(nat len)
  requires true;
  ensures true == no_dups(none_list_fp(len));
  {
    switch(len) {
      case zero:
        return;
      case succ(l): confirm_no_dups_on_nones(l);
    }
  }

  lemma void confirm_hash_list_for_nones<kt>(list<int> hashes,
                                             fixpoint (kt,int) hash)
  requires true;
  ensures true == hash_list(none_list_fp(nat_of_int(length(hashes))),
                            hashes, hash);
  {
    switch(hashes) {
      case nil:
        return;
      case cons(h,t):
        confirm_hash_list_for_nones(t, hash);
        nat_len_of_non_nil(h,t);
        assert(tail(none_list_fp(nat_of_int(length(hashes)))) ==
               none_list_fp(nat_of_int(length(t))));
        return;
    }
  }
  @*/

/*@
  predicate key_vals<kt,vt>(list<option<kt> > key_arr, list<vt> val_arr,
                            list<pair<kt,vt> > kvs) =
      switch (key_arr) {
        case nil: return val_arr == nil &*& kvs == nil;
        case cons(key,tail):
          return switch(key) {
            case none: return val_arr != nil &*&
                              key_vals(tail, tail(val_arr), kvs);
            case some(k): return
              val_arr != nil &*&
              true == mem(pair(k,head(val_arr)), kvs) &*&
              key_vals(tail, tail(val_arr), remove(pair(k,head(val_arr)), kvs));
          };
      };

  fixpoint bool rec_props<kt>(fixpoint (kt,int,bool) prop,
                              list<pair<kt,int> > recs) {
    switch (recs) {
      case nil: return true;
      case cons(rec,tail):
        return true == prop(fst(rec),snd(rec)) &&
                       rec_props(prop, tail);
    }
  }

  predicate mapping<kt>(list<pair<kt,int> > m,
                        list<pair<kt,void*> > addrs,
                        predicate (void*;kt) keyp,
                        fixpoint (kt,int,bool) recp,
                        fixpoint (kt,int) hash_entry,
                        fixpoint (kt, int) hash_offset,
                        int capacity,
                        int* busybits,
                        void** keyps,
                        entry_t* k_hashes,
                        int* values) =
     pointers(keyps, capacity, ?kps) &*&
     hmapping<kt>(keyp, hash_entry, hash_offset, capacity, busybits, kps, k_hashes, ?hm) &*&
     ints(values, capacity, ?val_arr) &*&
     true == rec_props(recp, m) &*&
     key_vals<kt,int>(hmap_ks_fp(hm), val_arr, m) &*&
     key_vals<kt,void*>(hmap_ks_fp(hm), kps, addrs);

  fixpoint bool no_dup_keys<kt,vt>(list<pair<kt,vt> > m) {
    switch(m) {
      case nil:
        return true;
      case cons(h,t):
        return (false == map_has_fp(t, fst(h))) && no_dup_keys(t);
    }
  }
  @*/

/*@
  lemma void produce_empty_key_vals<kt,vt>(list<vt> val_arr)
  requires true;
  ensures key_vals<kt,vt>(none_list_fp(nat_of_int(length(val_arr))),
                          val_arr, nil);
  {
    switch(val_arr) {
      case nil:
        close key_vals(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil);
        return;
      case cons(vh,vt):
        produce_empty_key_vals(vt);
        nat_len_of_non_nil(vh,vt);
        close key_vals(none_list_fp(nat_of_int(length(val_arr))),
                       val_arr, nil);
        return;
    }
  }

  @*/
void map_initialize /*@ <kt> @*/(int* busybits, map_keys_equality* eq,
    void** keyps, entry_t *khs, int* vals,
    int capacity)
  /*@ requires map_key_type<kt>(_) &*& map_key_hash_entry<kt>(?hash_entry) &*& map_key_hash_offset<kt>(?hash_offset) &*&
    [?fr]is_map_keys_equality<kt>(eq, ?keyp) &*&
    map_record_property<kt>(?recp) &*&
    ints(busybits, capacity, ?bbs) &*&
    pointers(keyps, capacity, ?kplist) &*&
    ints(vals, capacity, ?vallist) &*&
    uints(khs, capacity, ?khlist) &*&
    0 < capacity &*& 2*capacity < INT_MAX; @*/
  /*@ ensures mapping<kt>(empty_map_fp(), empty_map_fp(),
    keyp, recp, hash_entry, hash_offset,
    capacity, busybits, keyps,
    khs, vals) &*&
    [fr]is_map_keys_equality<kt>(eq, keyp); @*/
{
  //@ open map_key_type(_);
  //@ open map_key_hash_entry<kt>(_);
  //@ open map_key_hash_offset<kt>(_);
  //@ open map_record_property(_);
  int i = 0;
  for (; i < capacity; ++i)
    /*@ invariant [fr]is_map_keys_equality<kt>(eq, keyp) &*&
      ints(busybits, i, zero_list_fp(nat_of_int(i))) &*&
      ints(busybits + i, capacity - i, drop(i,bbs)) &*&
      pointers(keyps, capacity, kplist) &*&
      ints(vals, capacity, vallist) &*&
      uints(khs, capacity, khlist) &*&
      0 < capacity &*& 2*capacity < INT_MAX &*&
      0 <= i &*& i <= capacity;
      @*/
    //@ decreases capacity - i;
  {
    //@ move_int(busybits, i, capacity);
    //@ extend_zero_list(nat_of_int(i), head(drop(i,bbs)));
    busybits[i] = 0;
    //@ assert(succ(nat_of_int(i)) == nat_of_int(i+1));
    //@ tail_drop(bbs, i);
  }
  //@ assert(i == capacity);
  //@ assert(drop(i,bbs) == nil);
  //@ open(ints(busybits + i, capacity - i, drop(i,bbs)));
  //@ produce_pred_mapping<kt>(khlist, keyp, kplist);
  //@ confirm_no_dups_on_nones<kt>(nat_of_int(capacity));
  //@ confirm_hash_list_for_nones(khlist, hash_entry);
  //@ assert pointers(keyps, capacity, ?kps);
  //@ close hmapping<kt>(keyp, hash_entry, hash_offset, capacity, busybits, kps, khs, empty_hmap_fp<kt>(capacity, khlist));
  //@ produce_empty_key_vals<kt,int>(vallist);
  //@ produce_empty_key_vals<kt,void*>(kplist);
  /*@ close mapping(empty_map_fp(), empty_map_fp(), keyp, recp,
    hash_entry, hash_offset, capacity, busybits, keyps, khs, vals);
    @*/
}

/*@
  lemma void ks_mem_then_map_has<kt>(list<pair<kt,int> > m, kt key, int val)
  requires true == mem(pair(key, val), m);
  ensures true == map_has_fp(m, key);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == pair(key, val)) {
        } else {
          ks_mem_then_map_has(t, key, val);
        }
    }
  }
  @*/

/*@
  lemma void map_remove_unrelated_key<kt,vt>(list<pair<kt,vt> > m,
                                             kt k1, pair<kt,vt> kv2)
  requires k1 != fst(kv2);
  ensures map_has_fp(m, k1) == map_has_fp(remove(kv2, m), k1) &*&
          map_get_fp(m, k1) == map_get_fp(remove(kv2, m), k1);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == k1) {
        } else if (h == kv2) {
        } else {
          map_remove_unrelated_key(t, k1, kv2);
        }
    }
  }
  @*/

/*@
  lemma void kopts_has_then_keys_has<kt>(list<option<kt> > ks,
                                         list<pair<kt,int> > m, kt key)
  requires key_vals(ks, ?val_arr, m) &*& true == mem(some(key), ks);
  ensures key_vals(ks, val_arr, m) &*& true == map_has_fp(m, key);
  {
    switch(ks) {
      case nil: return;
      case cons(h,t):
        open key_vals(ks, val_arr, m);
        if (h == some(key)) {
          ks_mem_then_map_has(m, key, head(val_arr));
        } else {
          if (h == none) {
            kopts_has_then_keys_has(t, m, key);
          } else {
            kopts_has_then_keys_has(t, remove(pair(get_some(h),
                                                   head(val_arr)),
                                              m),
                                    key);
            map_remove_unrelated_key(m, key, pair(get_some(h), head(val_arr)));
          }
        }
        close key_vals(ks, val_arr, m);
    }
  }

  lemma void kopts_has_not_then_keys_has_not<kt>(list<option<kt> > ks,
                                                 list<pair<kt,int> > m, kt key)
  requires key_vals(ks, ?val_arr, m) &*& false == mem(some(key), ks);
  ensures key_vals(ks, val_arr, m) &*& false == map_has_fp(m, key);
  {
    switch(ks) {
      case nil:
        open key_vals(ks, val_arr, m);
        close key_vals(ks, val_arr, m);
        return;
      case cons(h,t):
        open key_vals(ks, val_arr, m);
        if (h == some(key)) {
        } else {
          if (h == none) {
            kopts_has_not_then_keys_has_not(t, m, key);
          } else {
            kopts_has_not_then_keys_has_not(t, remove(pair(get_some(h),
                                                           head(val_arr)),
                                                      m),
                                            key);
            map_remove_unrelated_key(m, key, pair(get_some(h), head(val_arr)));
          }
        }
        close key_vals(ks, val_arr, m);
        return;
    }
  }

  lemma void hmap_exists_iff_map_has<kt>(hmap<kt> hm,
                                         list<pair<kt,int> > m, kt k)
  requires key_vals(hmap_ks_fp(hm), ?val_arr, m);
  ensures key_vals(hmap_ks_fp(hm), val_arr, m) &*&
          map_has_fp(m, k) == hmap_exists_key_fp(hm, k);
  {
    if (hmap_exists_key_fp(hm, k)) {
      kopts_has_then_keys_has(hmap_ks_fp(hm), m, k);
      assert(true == hmap_exists_key_fp(hm, k));
      assert(true == map_has_fp(m, k));
    } else {
      kopts_has_not_then_keys_has_not(hmap_ks_fp(hm), m, k);
    }
  }

  lemma void hmapping_ks_capacity<kt>(hmap<kt> hm, int capacity)
  requires hmapping<kt>(?kp, ?hsh_entry, ?hsh_offset, capacity, ?busybits, ?kps,
                        ?khs, hm);
  ensures hmapping<kt>(kp, hsh_entry, hsh_offset, capacity, busybits, kps,
                       khs, hm) &*&
          length(hmap_ks_fp(hm)) == capacity;
  {
    open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, khs, hm);
    assert pred_mapping(?pts, ?bbs, kp, hmap_ks_fp(hm));
    pred_mapping_same_len(bbs, hmap_ks_fp(hm));
    close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, khs, hm);
  }
  @*/

/*@
  lemma void remove_unique_no_dups<kt,vt>(list<pair<kt,vt> > m,
                                          pair<kt,vt> kv)
  requires false == map_has_fp(remove(kv, m), fst(kv));
  ensures no_dup_keys(m) == no_dup_keys(remove(kv, m));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
          assert(remove(kv, m) == t);
        } else {
          remove_unique_no_dups(t, kv);
          assert(remove(kv, m) == cons(h, remove(kv, t)));
          assert(m == cons(h,t));
          if (no_dup_keys(remove(kv,m))) {
            assert(true == no_dup_keys(t));
            assert(false == map_has_fp(remove(kv, t), fst(h)));
            map_remove_unrelated_key(t, fst(h), kv);
            assert(false == map_has_fp(t, fst(h)));
            assert(true == no_dup_keys(m));
          } else {
            if (map_has_fp(remove(kv,t),fst(h))) {
              map_remove_unrelated_key(t, fst(h), kv);
              assert(true == map_has_fp(t, fst(h)));
            } else {
              assert(false == no_dup_keys(remove(kv,t)));
            }
          }
        }
    }
  }

  lemma void hmap2map_no_key<kt,vt>(list<option<kt> > ks,
                                    list<pair<kt,vt> > m,
                                    kt key)
  requires key_vals(ks, ?va, m) &*& false == mem(some(key), ks);
  ensures key_vals(ks, va, m) &*& false == map_has_fp(m, key);
  {
    open key_vals(ks, va, m);
    switch(ks) {
      case nil:
        break;
      case cons(h,t):
        if (h == none) {
          hmap2map_no_key(t, m, key);
        } else {
          hmap2map_no_key(t, remove(pair(get_some(h), head(va)), m), key);
          map_remove_unrelated_key(m, key, pair(get_some(h), head(va)));
        }
    }
    close key_vals(ks, va, m);
  }

  lemma void map_no_dups<kt,vt>(list<option<kt> > ks, list<pair<kt,vt> > m)
  requires key_vals(ks, ?val_arr, m) &*& true == no_dups(ks);
  ensures key_vals(ks, val_arr, m) &*& true == no_dup_keys(m);
  {
    open key_vals(ks, val_arr, m);
    switch(ks) {
      case nil:
        break;
      case cons(h,t):
        if (h == none) {
          map_no_dups(t, m);
        } else {
          map_no_dups(t, remove(pair(get_some(h), head(val_arr)), m));
          hmap2map_no_key(t, remove(pair(get_some(h), head(val_arr)), m),
                          get_some(h));
          remove_unique_no_dups(m, pair(get_some(h), head(val_arr)));
        }
    }
    close key_vals(ks, val_arr, m);
  }
  @*/

/*@
  lemma void map_has_this_key<kt,vt>(list<pair<kt,vt> > m, pair<kt,vt> kv)
  requires true == mem(kv, m);
  ensures true == map_has_fp(m, fst(kv));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
        } else {
          map_has_this_key(t, kv);
        }
    }
  }

  lemma void map_no_dups_returns_the_key<kt,vt>(list<pair<kt, vt> > m,
                                                pair<kt, vt> kv)
  requires true == mem(kv, m) &*& true == no_dup_keys(m);
  ensures map_get_fp(m, fst(kv)) == snd(kv);
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (h == kv) {
        } else {
          map_has_this_key(t, kv);
          assert(true == map_has_fp(t, fst(kv)));
          if (fst(h) == fst(kv)) {
          }
          assert(fst(h) != fst(kv));
          map_no_dups_returns_the_key(t, kv);
        }
    }
  }
  @*/

/*@
  lemma void ks_find_returns_the_key<kt,vt>(list<option<kt> > ks,
                                            list<vt> val_arr,
                                            list<pair<kt, vt> > m, kt k)
  requires key_vals(ks, val_arr, m) &*& true == no_dups(ks) &*&
           true == mem(some(k), ks);
  ensures key_vals(ks, val_arr, m) &*&
          nth(index_of(some(k), ks), val_arr) == map_get_fp(m, k);
  {
    switch(ks) {
      case nil:
        open key_vals(ks, val_arr, m);
        close key_vals(ks, val_arr, m);
      case cons(h,t):
        map_no_dups(ks, m);
        open key_vals(ks, val_arr, m);
        if (h == some(k)) {
          nth_0_head(val_arr);
          assert(index_of(some(k), ks) == 0);
          assert(nth(0, val_arr) == head(val_arr));
          assert(nth(index_of(some(k), ks), val_arr) == head(val_arr));
          assert(true == mem(pair(k,head(val_arr)), m));
          map_no_dups_returns_the_key(m, pair(k, head(val_arr)));
          assert(map_get_fp(m, k) == head(val_arr));
        } else if (h == none) {
          ks_find_returns_the_key(t, tail(val_arr), m, k);
          assert(val_arr != nil);
          mem_index_of(some(k), t);
          nth_cons(index_of(some(k), t) + 1, tail(val_arr), head(val_arr));
          cons_head_tail(val_arr);
        } else {
          ks_find_returns_the_key(t, tail(val_arr),
                                  remove(pair(get_some(h),
                                              head(val_arr)),
                                         m),
                                  k);
          map_remove_unrelated_key(m, k, pair(get_some(h), head(val_arr)));
          assert(index_of(some(k), ks) == 1 + index_of(some(k), t));

          assert(val_arr != nil);
          mem_index_of(some(k), t);
          nth_cons(index_of(some(k), t) + 1, tail(val_arr), head(val_arr));
          cons_head_tail(val_arr);
        }
        close key_vals(ks, val_arr, m);
    }
  }

  lemma void hmap_find_returns_the_key<kt,vt>(hmap<kt> hm,
                                              list<vt> val_arr,
                                              list<pair<kt, vt> > m, kt k)
  requires key_vals(hmap_ks_fp(hm), val_arr, m) &*&
           true == no_dups(hmap_ks_fp(hm)) &*&
           true == hmap_exists_key_fp(hm, k);
  ensures key_vals(hmap_ks_fp(hm), val_arr, m) &*&
          nth(hmap_find_key_fp(hm, k), val_arr) == map_get_fp(m, k);
  {
    ks_find_returns_the_key(hmap_ks_fp(hm), val_arr, m, k);
  }
  @*/

/*@
  lemma void map_extract_recp<kt>(list<pair<kt,int> > m, kt k,
                                  fixpoint(kt,int,bool) prop)
  requires true == rec_props(prop, m) &*& true == map_has_fp(m, k);
  ensures true == prop(k, map_get_fp(m, k));
  {
    switch(m) {
      case nil: return;
      case cons(h,t):
        if (fst(h) == k) {
        } else {
          map_extract_recp(t, k, prop);
        }
    }
  }
  @*/
int map_get /*@ <kt> @*/(int* busybits, void** keyps, entry_t *k_hashes, int* values,
    void* keyp, map_keys_equality* eq, entry_t hash_entry, offset_t hash_offset, int* value,
    unsigned int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh_entry, ?hsh_offset, capacity, busybits,
                         keyps, k_hashes, values) &*&
             kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality(eq, kp) &*&
             hsh_entry(k) == hash_entry &*&
             hsh_offset(k) == hash_offset &*&
             *value |-> ?v &*&
             coprime(hash_offset, capacity) &*&
             hash_offset > 0 &*& hash_offset < capacity; @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits,
                        keyps, k_hashes, values) &*&
            kp(keyp, k) &*&
            [fr]is_map_keys_equality(eq, kp) &*&
            (map_has_fp(m, k) ?
             (result == 1 &*&
              *value |-> ?nv &*&
              nv == map_get_fp(m, k) &*&
              true == recp(k, nv)):
             (result == 0 &*&
              *value |-> v)) &*&
              coprime(hash_offset, capacity); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, ?kps, k_hashes, ?hm);
  unsigned int start = loop(hash_entry, capacity);
  //@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  int index = find_key(busybits, keyps, k_hashes, start,
      keyp, eq, hash_entry, hash_offset, capacity);
  //@ hmap_exists_iff_map_has(hm, m, k);
  if (-1 == index)
  {
    //@ close mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
    return 0;
  }
  //@ hmapping_ks_capacity(hm, capacity);
  //@ assert(index < capacity);
  //@ assert(ints(values, capacity, ?val_arr));
  *value = values[index];
  //@ hmap_find_returns_the_key(hm, val_arr, m, k);
  //@ map_extract_recp(m, k, recp);
  //@ close mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
  return 1;
}

/*@
  lemma void ks_map_size<kt>(list<option<kt> > ks, list<pair<kt,int> > m)
  requires key_vals(ks, ?va, m);
  ensures key_vals(ks, va, m) &*&
          ks_size_fp(ks) == map_size_fp(m);
  {
    open key_vals(ks, va, m);
    switch(ks) {
      case nil:
      case cons(h,t):
        if (h == none) {
          ks_map_size(t, m);
        } else {
          ks_map_size(t, remove(pair(get_some(h), head(va)), m));
        }

    }
    close key_vals(ks, va, m);
  }

  lemma void hmap_map_size<kt>(hmap<kt> hm, list<pair<kt,int> > m)
  requires key_vals(hmap_ks_fp(hm), ?va, m);
  ensures key_vals(hmap_ks_fp(hm), va, m) &*&
          hmap_size_fp(hm) == map_size_fp(m);
  {
    ks_map_size(hmap_ks_fp(hm), m);
  }
  @*/

/*@
  lemma void put_keeps_pred_mapping<kt>(list<void*> pts, list<int> bbs,
                                        predicate (void*; kt) pred,
                                        list<option<kt> > ks,
                                        int index, void* kp, kt k)
  requires pred_mapping(pts, bbs, pred, ks) &*& [0.5]pred(kp, k) &*&
           0 <= index &*& index < length(bbs) &*&
           nth(index, ks) == none;
  ensures pred_mapping(update(index, kp, pts), update(index, 1, bbs),
                       pred, update(index, some(k), ks));
  {
    open pred_mapping(pts, bbs, pred, ks);
    switch(bbs) {
      case nil: break;
      case cons(bbh, bbt):
        if (index == 0) {
          tail_of_update_0(pts, kp);
          tail_of_update_0(ks, some(k));
          head_update_0(kp, pts);
        } else {
          put_keeps_pred_mapping(tail(pts), bbt, pred, tail(ks),
                                 index-1, kp, k);
          cons_head_tail(pts);
          cons_head_tail(ks);
          update_tail_tail_update(head(pts), tail(pts), index, kp);
          update_tail_tail_update(head(ks), tail(ks), index, some(k));
          update_tail_tail_update(bbh, bbt, index, 1);
        }
        update_non_nil(pts, index, kp);
        update_non_nil(ks, index, some(k));
    }
    close pred_mapping(update(index, kp, pts), update(index, 1, bbs),
                       pred, update(index, some(k), ks));
  }
  @*/

/*@
  lemma void put_preserves_no_dups<kt>(list<option<kt> > ks, int i, kt k)
  requires false == mem(some(k), ks) &*& true == no_dups(ks);
  ensures true == no_dups(update(i, some(k), ks));
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          put_preserves_no_dups(t, i-1, k);
          if (h == none) {
          } else {
            assert(false == mem(h, t));
            update_irrelevant_cell(h, i-1, some(k), t);
            assert(false == mem(h, update(i-1, some(k), t)));
          }
        }
    }
  }
  @*/

/*@
  lemma void hmap_coherent_hash_update<kt>(list<option<kt> > ks, list<int> khs,
                                           fixpoint (kt,int) hash,
                                           int index, kt nk, int nhsh)
  requires true == hash_list(ks, khs, hash) &*& hash(nk) == nhsh &*&
           0 <= index;
  ensures true == hash_list(update(index, some(nk), ks),
                            update(index, nhsh, khs), hash);
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        update_non_nil(khs, index, nhsh);
        if (index == 0) {
          head_update_0(some(nk), ks);
          head_update_0(nhsh, khs);
          tail_of_update_0(khs, nhsh);
          assert(update(0, nhsh, khs) != nil);
          assert(true == hash_list(t, tail(update(0, nhsh, khs)), hash));
          assert(head(update(0, nhsh, khs)) == hash(get_some(head(update(0, some(nk), ks)))));
        } else {
          hmap_coherent_hash_update(t, tail(khs), hash, index-1, nk, nhsh);
          cons_head_tail(khs);
          update_tail_tail_update(head(khs), tail(khs), index, nhsh);
          update_tail_tail_update(h, t, index, some(nk));
        }
    }
  }
  @*/

/*@
  lemma void put_remove_interchangable<kt,vt>(list<pair<kt,vt> > m,
                                              pair<kt,vt> kv1,
                                              kt k2, vt v2)
  requires fst(kv1) != k2;
  ensures map_put_fp(remove(kv1, m), k2, v2) ==
          remove(kv1, (map_put_fp(m, k2, v2)));
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
        }
    }
  }

  lemma void coherent_put_preserves_key_vals<kt,vt>(list<option<kt> > ks,
                                                    list<vt> vals,
                                                    list<pair<kt,vt> > m,
                                                    int i, kt k, vt v)
  requires key_vals(ks, vals, m) &*&
           nth(i, ks) == none &*& 0 <= i &*&
           false == mem(some(k), ks);
  ensures key_vals(update(i, some(k), ks), update(i, v, vals),
                   map_put_fp(m, k, v));
  {
    open key_vals(ks, vals, m);
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
          assert(true == mem(pair(k,v), map_put_fp(m, k, v)));
          assert(head(update(i, some(k), ks)) == some(k));
          head_update_0(v, vals);
          assert(head(update(i, v, vals)) == v);
          tail_of_update_0(vals, v);
          tail_of_update_0(ks, some(k));
          assert(remove(pair(k,v), map_put_fp(m, k, v)) == m);
        } else {
          update_tail_tail_update(head(vals), tail(vals), i, v);
          update_tail_tail_update(h, t, i, some(k));
          cons_head_tail(vals);
          if (h == none) {
            coherent_put_preserves_key_vals(t, tail(vals), m, i-1, k, v);
          } else {
            coherent_put_preserves_key_vals(t, tail(vals),
                                            remove(pair(get_some(h),
                                                        head(vals)),
                                                   m),
                                            i-1, k, v);
            assert(head(update(i, some(k), ks)) == h);
            head_update_nonzero(i, v, vals);
            assert(head(update(i, v, vals)) == head(vals));
            assert(true == mem(pair(get_some(h),head(vals)), map_put_fp(m, k, v)));

            //assert(false == mem(pair(get_some(h), head(vals)), m));
            assert(get_some(h) != k);
            put_remove_interchangable(m, pair(get_some(h), head(vals)), k, v);
            assert(map_put_fp(remove(pair(get_some(h), head(vals)), m), k, v) ==
                   remove(pair(get_some(h), head(vals)), (map_put_fp(m, k, v))));
          }
        }
        update_non_nil(vals, i, v);
    }
    close key_vals(update(i, some(k), ks), update(i, v, vals),
                   map_put_fp(m, k, v));
  }
  @*/
int map_put /*@ <kt> @*/(int* busybits, void** keyps, entry_t *k_hashes, int* values,
    void* keyp, entry_t hash_entry, offset_t hash_offset, int value,
    unsigned int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh_entry, ?hsh_offset, capacity, busybits,
                         keyps, k_hashes, values) &*&
             [0.5]kp(keyp, ?k) &*& true == recp(k, value) &*&
             hsh_entry(k) == hash_entry &*&
             hsh_offset(k) == hash_offset &*&
             false == map_has_fp(m, k) &*&
             hash_offset > 0 &*& hash_offset < capacity &*& coprime(hash_offset, capacity); @*/
/*@ ensures true == recp(k, value) &*&
            (map_size_fp(m) < capacity ?
             (result == 1 &*&
              mapping<kt>(map_put_fp(m, k, value),
                          map_put_fp(addrs, k, keyp),
                          kp, recp,
                          hsh_entry, hsh_offset, 
                          capacity, busybits,
                          keyps, k_hashes, values)) :
             (result == 0 &*&
              [0.5]kp(keyp, k) &*&
              mapping<kt>(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits,
                          keyps, k_hashes, values))) &*&
              coprime(hash_offset, capacity); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, ?kps, k_hashes, ?hm);
  unsigned int start = loop(hash_entry, capacity);
  //@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  int index = find_empty(busybits, start, hash_entry, hash_offset, capacity);

  //@ hmap_map_size(hm, m);
  if (-1 == index)
  {
    //@ close mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
    return 0;
  }
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  //@ assert pred_mapping(kps, ?bbs, kp, ?ks);
  //@ put_keeps_pred_mapping(kps, bbs, kp, ks, index, keyp, k);
  //@ hmap_exists_iff_map_has(hm, m, k);
  //@ put_preserves_no_dups(ks, index, k);
  //@ assert(hm == hmap(ks, ?khs));
  //@ assert(ints(values, capacity, ?vals));
  //@ hmap_coherent_hash_update(ks, khs, hsh_entry, index, k, hash_entry);
  busybits[index] = 1;
  keyps[index] = keyp;
  k_hashes[index] = hash_entry;
  values[index] = value;
  /*@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, update(index, keyp, kps),
                     k_hashes, hmap_put_key_fp(hm, index, k, hash_entry));
    @*/
  //@ coherent_put_preserves_key_vals(hmap_ks_fp(hm), vals, m, index, k, value);
  //@ coherent_put_preserves_key_vals(hmap_ks_fp(hm), kps, addrs, index, k, keyp);
  /*@ close mapping(map_put_fp(m, k, value), map_put_fp(addrs, k, keyp),
                    kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
    @*/
  return 1;
}

/*@
  lemma void hmap_rem_preserves_pred_mapping<kt>(list<char*> kps, list<int> bbs,
                                                 predicate (void*;kt) keyp,
                                                 list<option<kt> > ks,
                                                 int i)
  requires pred_mapping(kps, bbs, keyp, ks) &*& 0 <= i &*& nth(i, ks) == some(?k);
  ensures pred_mapping(kps, update(i, 0, bbs), keyp, update(i, none, ks)) &*&
          [0.5]keyp(nth(i, kps), k);
  {
    open pred_mapping(kps, bbs, keyp, ks);
    switch(bbs) {
      case nil: break;
      case cons(bbh, bbt):
        cons_head_tail(ks);
        cons_head_tail(kps);
        if (i == 0) {
        } else {
          hmap_rem_preserves_pred_mapping(tail(kps), bbt, keyp, tail(ks), i-1);
          nth_cons(i, tail(ks), head(ks));
          nth_cons(i, tail(kps), head(kps));
        }
    }
    close pred_mapping(kps, update(i, 0, bbs), keyp, update(i, none, ks));
  }


  lemma void rem_preserves_no_mem<kt>(list<option<kt> > ks, kt k, int i)
  requires false == mem(some(k), ks);
  ensures false == mem(some(k), update(i, none, ks));
  {
    switch(ks) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          rem_preserves_no_mem(t, k, i-1);
        }
    }
  }

  lemma void hmap_rem_preserves_no_dups<kt>(list<option<kt> > ks, int i)
  requires true == no_dups(ks) &*& 0 <= i;
  ensures true == no_dups(update(i, none, ks));
  {
    switch(ks) {
     case nil: return;
     case cons(h,t):
       if (i == 0) {
       } else {
         hmap_rem_preserves_no_dups(t, i-1);
         if (h == none){
         } else {
           assert(false == mem(h, t));
           some_get_some(h);
           rem_preserves_no_mem(t, get_some(h), i-1);
         }
       }
       return;
    }
  }

  lemma void hmap_rem_preserves_hash_list<kt>(list<option<kt> > vals,
                                              list<int> hashes,
                                              fixpoint (kt, int) hash,
                                              int i)
  requires true == hash_list(vals, hashes, hash) &*& 0 <= i;
  ensures true == hash_list(update(i, none, vals), hashes, hash);
  {
    switch(vals){
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          hmap_rem_preserves_hash_list(t, tail(hashes), hash, i-1);
        }
    }
  }
  @*/

/*@
  lemma void map_erase_preserves_rec_props<kt>(list<pair<kt,int> > m,
                                               fixpoint(kt,int,bool) recp,
                                               kt k)
  requires true == rec_props(recp, m);
  ensures true == rec_props(recp, map_erase_fp(m, k));
  {
    switch(m) {
      case nil:
      case cons(h,t):
        if (fst(h) == k) {
        } else {
          map_erase_preserves_rec_props(t, recp, k);
        }
    }
  }
  @*/

/*@
  lemma void map_has_not_mem_not<kt,vt>(list<pair<kt,vt> > m,
                                        kt k, vt v)
  requires false == map_has_fp(m, k);
  ensures false == mem(pair(k,v), m);
  {
    switch(m){
      case nil: break;
      case cons(h,t):
        map_has_not_mem_not(t, k, v);
    }
  }

  lemma void map_no_dups_has_that_pair<kt,vt>(pair<kt,vt> mh,
                                              list<pair<kt,vt> > mt,
                                              kt k, vt v)
  requires true == no_dup_keys(cons(mh,mt)) &*&
           true == mem(pair(k,v), cons(mh,mt)) &*&
           fst(mh) == k;
  ensures mh == pair(k,v);
  {
    if (mh != pair(k,v)) {
      assert(false == map_has_fp(mt, fst(mh)));
      map_has_not_mem_not(mt, k, v);
    }
  }

  lemma void map_erase_that_key<kt,vt>(list<pair<kt,vt> > m,
                                       kt k, vt v)
  requires true == no_dup_keys(m) &*& true == mem(pair(k, v), m);
  ensures map_erase_fp(m, k) == remove(pair(k, v), m);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (fst(h) == k) {
          map_no_dups_has_that_pair(h, t, k, v);
          assert(h == pair(k,v));
        } else {
          map_erase_that_key(t, k, v);
        }
    }
  }

  lemma void map_erase_unrelated_key<kt,vt>(list<pair<kt,vt> > m,
                                             pair<kt,vt> kv1, kt k2)
  requires fst(kv1) != k2;
  ensures mem(kv1, m) == mem(kv1, map_erase_fp(m, k2)) &*&
          remove(kv1, map_erase_fp(m, k2)) == map_erase_fp(remove(kv1, m), k2);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
          if (fst(h) == k2) {
          } else {
            map_erase_unrelated_key(t, kv1, k2);
          }
        }
    }
  }

  lemma void map_erase_remove_unrelated<kt>(list<pair<kt,int> > m,
                                            pair<kt,int> kv1, kt k2)
  requires fst(kv1) != k2;
  ensures remove(kv1, map_erase_fp(m, k2)) == map_erase_fp(remove(kv1, m), k2);
  {
    switch(m) {
      case nil: break;
      case cons(h,t):
        if (h == kv1) {
        } else {
          if (fst(h) == k2) {
          } else {
            map_erase_remove_unrelated(t, kv1, k2);
          }
        }
    }
  }

  lemma void ks_rem_map_erase_coherent<kt,vt>(list<option<kt> > ks,
                                              list<pair<kt,vt> > m,
                                              int i, kt k)
  requires key_vals(ks, ?vals, m) &*& nth(i, ks) == some(k) &*&
           true == no_dup_keys(m) &*& true == no_dups(ks) &*&
           0 <= i &*& i < length(ks);
  ensures key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
  {
    switch(ks) {
      case nil:
        open key_vals(ks, vals, m);
        close key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
        break;
      case cons(h,t):
        open key_vals(ks, vals, m);
        if (i == 0) {
          tail_of_update_0(ks, none);
          assert(h == some(k));
          assert(true == mem(pair(k, head(vals)), m));
          map_erase_that_key(m, k, head(vals));
          assert(map_erase_fp(m, k) == remove(pair(k, head(vals)), m));
        } else {
          if (h == none) {
            ks_rem_map_erase_coherent(t, m, i-1, k);
          } else {
            hmap2map_no_key(t, remove(pair(get_some(h), head(vals)), m),
                            get_some(h));
            remove_unique_no_dups(m, pair(get_some(h), head(vals)));
            ks_rem_map_erase_coherent(t, remove(pair(get_some(h),
                                                     head(vals)), m),
                                      i-1, k);

            map_erase_unrelated_key(m, pair(get_some(h), head(vals)), k);
            update_tail_tail_update(h, t, i, none);
          }
        }
        close key_vals(update(i, none, ks), vals, map_erase_fp(m, k));
    }
  }

  lemma void hmap_ks_hmap_rm<kt>(hmap<kt> hm, int i)
  requires true;
  ensures hmap_ks_fp(hmap_rem_key_fp(hm, i)) == update(i, none, hmap_ks_fp(hm));
  {
    switch(hm) {
      case hmap(ks, khs): break;
    }
  }

  lemma void hmap_rem_map_erase_coherent<kt,vt>(hmap<kt> hm,
                                                list<pair<kt, vt> > m,
                                                int i, kt k)
  requires key_vals(hmap_ks_fp(hm), ?vals, m) &*&
           nth(i, hmap_ks_fp(hm)) == some(k) &*&
           true == no_dups(hmap_ks_fp(hm)) &*&
           0 <= i &*& i < length(hmap_ks_fp(hm));
  ensures key_vals(hmap_ks_fp(hmap_rem_key_fp(hm, i)),
                   vals, map_erase_fp(m, k));
  {
     map_no_dups(hmap_ks_fp(hm), m);
     hmap_ks_hmap_rm(hm, i);
     ks_rem_map_erase_coherent(hmap_ks_fp(hm), m, i, k);
  }
  @*/
int map_erase /*@ <kt> @*/(int* busybits, void** keyps, entry_t *k_hashes, void* keyp,
    map_keys_equality* eq, entry_t hash_entry, offset_t hash_offset, unsigned int capacity,
    void** keyp_out)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh_entry, ?hsh_offset, capacity, busybits,
                         keyps, k_hashes, ?values) &*&
             [0.5]kp(keyp, ?k) &*&
             [?fr]is_map_keys_equality<kt>(eq, kp) &*&
             hsh_entry(k) == hash_entry &*&
             hsh_offset(k) == hash_offset &*&
             *keyp_out |-> ?ko &*&
             hash_offset > 0 &*& hash_offset < capacity &*& coprime(hash_offset, capacity); @*/
/*@ ensures [0.5]kp(keyp, k) &*&
            [fr]is_map_keys_equality<kt>(eq, kp) &*&
            (map_has_fp(m, k) ?
              (result == 1 &*&
               *keyp_out |-> ?nko &*&
               nko == map_get_fp(addrs, k) &*&
               [0.5]kp(nko, k) &*&
               mapping<kt>(map_erase_fp(m, k), map_erase_fp(addrs, k),
                           kp, recp, hsh_entry, hsh_offset,
                           capacity, busybits, keyps, k_hashes, values)) :
              (result == 0 &*&
               *keyp_out |-> ko &*&
               mapping<kt>(m, addrs, kp, recp, hsh_entry, hsh_offset,
                           capacity, busybits, keyps, k_hashes, values))) &*&
             coprime(hash_offset, capacity); @*/
{
  //@ open mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, ?kps, k_hashes, ?hm);
  unsigned int start = loop(hash_entry, capacity);
  //@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  int index = find_key(busybits, keyps, k_hashes, start,
      keyp, eq, hash_entry, hash_offset, capacity);
  //@ hmap_exists_iff_map_has(hm, m, k);
  if (-1 == index)
  {
    //@ close mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
    return 0;
  }
  //@ hmapping_ks_capacity(hm, capacity);
  //@ assert(index < capacity);
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  //@ assert(pred_mapping(kps, ?bbs, kp, ?ks));
  //@ assert(uints(k_hashes, capacity, ?khs));
  busybits[index] = 0;
  *keyp_out = keyps[index];
  //@ hmap_find_returns_the_key(hm, kps, addrs, k);
  //@ mem_nth_index_of(some(k), ks);
  //@ hmap_rem_preserves_pred_mapping(kps, bbs, kp, ks, index);
  //@ hmap_rem_preserves_no_dups(ks, index);
  //@ hmap_rem_preserves_hash_list(ks, khs, hsh_entry, index);
  //@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hmap_rem_key_fp(hm, index));
  //@ map_erase_preserves_rec_props(m, recp, k);
  //@ hmap_rem_map_erase_coherent(hm, m, index, k);
  //@ hmap_rem_map_erase_coherent(hm, addrs, index, k);
  /*@ close mapping(map_erase_fp(m, k), map_erase_fp(addrs, k),
                    kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
    @*/
  //@ assert true == map_has_fp(m, k);
  return 1;
}

/*@
  fixpoint bool nonzero(int x) { return x != 0; }

  lemma void add_bit_to_nonzero_count(list<int> bbs, int i, int s)
  requires s == count(take(i, bbs), nonzero) &*& 0 <= i &*& i < length(bbs);
  ensures nth(i, bbs) == 0 ?
           s == count(take(i+1, bbs), nonzero) :
           s+1 == count(take(i+1, bbs), nonzero);
  {
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        if (i == 0) {
        } else {
          if (h == 0) {
            add_bit_to_nonzero_count(t, i-1, s);
          } else {
            add_bit_to_nonzero_count(t, i-1, s-1);
          }
        }
    }
  }

  lemma void nonzero_count_is_ks_size<kt>(list<int> bbs, list<option<kt> > ks)
  requires pred_mapping(?kps, bbs, ?pred, ks);
  ensures pred_mapping(kps, bbs, pred, ks) &*&
          count(bbs, nonzero) == ks_size_fp(ks);
  {
    open pred_mapping(kps, bbs, pred, ks);
    switch(bbs) {
      case nil: break;
      case cons(h,t):
        nonzero_count_is_ks_size(t, tail(ks));
    }
    close pred_mapping(kps, bbs, pred, ks);
  }
  @*/
int map_size /*@ <kt> @*/ (int* busybits, int capacity)
/*@ requires mapping<kt>(?m, ?addrs, ?kp, ?recp, ?hsh_entry, ?hsh_offset, capacity, busybits,
                         ?keyps, ?k_hashes, ?values); @*/
/*@ ensures mapping<kt>(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits,
                        keyps, k_hashes, values) &*&
            result == map_size_fp(m);@*/
{
  //@ open mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
  //@ open hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, ?kps, k_hashes, ?hm);
  //@ assert ints(busybits, capacity, ?bbs);
  //@ assert pointers(keyps, capacity, kps);
  //@ assert uints(k_hashes, capacity, ?khs);
  //@ assert pred_mapping(kps, bbs, kp, ?ks);
	int s = 0;
	int i = 0;
	for (; i < capacity; ++i)
    /*@ invariant 0 <= i &*& i <= capacity &*&
                  0 < capacity &*& 2*capacity < INT_MAX &*&
                  ints(busybits, capacity, bbs) &*&
                  pointers(keyps, capacity, kps) &*&
                  uints(k_hashes, capacity, khs) &*&
                  pred_mapping(kps, bbs, kp, ks) &*&
                  true == no_dups(ks) &*&
                  true == hash_list(ks, khs, hsh_entry) &*&
                  hm == hmap(ks, khs) &*&
                  count(take(i, bbs), nonzero) == s &*&
                  0 <= s &*& s <= i;
      @*/
    //@ decreases capacity - i;
	{
    //@ add_bit_to_nonzero_count(bbs, i, s);
		if (busybits[i] != 0)
		{
			++s;
		}
	}
  //@ nonzero_count_is_ks_size(bbs, ks);
  //@ assert(s == hmap_size_fp(hm));
  //@ hmap_map_size(hm, m);
  //@ close hmapping(kp, hsh_entry, hsh_offset, capacity, busybits, kps, k_hashes, hm);
  //@ close mapping(m, addrs, kp, recp, hsh_entry, hsh_offset, capacity, busybits, keyps, k_hashes, values);
	return s;
}

/*@
  lemma void map_get_keeps_recp<kt>(list<pair<kt,int> > m, kt k)
  requires mapping(m, ?addrs, ?kp, ?rp, ?hsh_entry, ?hsh_offset,
                   ?cap, ?bbs, ?kps, ?khs, ?vals) &*&
           true == map_has_fp(m, k);
  ensures true == rp(k, map_get_fp(m, k)) &*&
          mapping(m, addrs, kp, rp, hsh_entry, hsh_offset,
                  cap, bbs, kps, khs, vals);
  {
    open mapping(m, addrs, kp, rp, hsh_entry, hsh_offset, cap, bbs, kps, khs, vals);
    map_extract_recp(m, k, rp);
    close mapping(m, addrs, kp, rp, hsh_entry, hsh_offset, cap, bbs, kps, khs, vals);
  }
  @*/
