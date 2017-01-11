int i = 0;
for (; i < capacity; ++i)
/*@ invariant ... &*& 
	true == up_to(nat_of_int(i),
		(byLoopNthProp)(ks, (not_my_key)(k),
			capacity, start));
@*/
//@ decreases capacity - i;
{
	int index = loop(start + i, capacity);
	int bb = busybits[index];
	int kh = k_hashes[index];
	void* kp = keyps[index];
	if (bb != 0 && kh == key_hash) {
		if (eq(kp, keyp)) {
			//@ hmap_find_this_key(hm, index, k);
			return index;
		}
	} else {
		//@ if (bb != 0) no_hash_no_key(ks, khs, k, index, hsh);
		//@ if (bb == 0) no_bb_no_key(ks, bbs, index);
	}
	//@ assert(true == not_my_key(k, nth(index, ks)));
}
/*@ by_loop_for_all(ks, (not_my_key)(k), 
	start, capacity, nat_of_int(capacity));
@*/
/*@ assert true == up_to(nat_of_int(length(ks)), 
	(nthProp)(ks, (not_my_key)(k))); 
@*/
//@ no_key_found(ks, k);
