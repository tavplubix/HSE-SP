
/*@ predicate Sorted{L}(int *t, integer a, integer b) =
  @     \forall integer i, j; a <= i <= j <= b ==> t[i] <= t[j];
  @*/

/*@ predicate Swap{L1,L2}(int *a, integer i, integer j) =
  @     \at(a[i],L1) == \at(a[j],L2) &&
  @     \at(a[j],L1) == \at(a[i],L2) &&
  @     \forall integer k; k != i && k != j ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ inductive Permut{L1,L2}(int *a, integer l, integer h) {
  @     case Permut_refl{L}:
  @         \forall int *a, integer l, h;
  @         Permut{L,L}(a, l, h);
  @     case Permut_sym{L1,L2}:
  @         \forall int *a, integer l, h;
  @         Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h);
  @     case Permut_trans{L1,L2,L3}:
  @         \forall int *a, integer l, h;
  @         Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==> Permut{L1,L3}(a, l, h);
  @     case Permut_swap{L1,L2}:
  @         \forall int *a, integer l, h, i, j;
  @         l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==> Permut{L1,L2}(a, l, h);
  @ }
  @*/


/*@ predicate shifted{L1, L2}(integer s, int* a, integer beg, integer end) =
  @     \forall integer k ; beg <= k <= end ==> \at(a[k], L1) == \at(a[s+k], L2);
  @*/

/*@ predicate unchanged{L1, L2}(int* a, integer beg, integer end) =
  @     shifted{L1, L2}(0, a, beg, end);
  @*/

/*@ lemma unchanged_is_permutation{L1, L2}:
  @     \forall int* a, integer beg, integer end;
  @         unchanged{L1, L2}(a, beg, end) ==> Permut{L1, L2}(a, beg, end); 
  @*/

/*@ lemma union_permutation{L1, L2}:
  @     \forall int* a, integer beg, split, end, int v;
  @         beg <= split <= end ==> Permut{L1, L2}(a, beg, split-1) ==>
  @         Permut{L1, L2}(a, split, end) ==>
  @         Permut{L1, L2}(a, beg, end);
  @*/


/*@ requires beg < last && \valid(a + (beg .. last));
  @ requires Sorted(a, beg, last - 1);
  @
  @ assigns a[ beg .. last ]; 
  @
  @ ensures Permut{Old, Post}(a, beg, last);
  @ ensures Sorted(a, beg, last);
  @*/
void insert(int *a, size_t beg, size_t last)
{
	size_t i = last;
	int value = a[i];

	/*@
	  loop invariant beg <= i <= last ;
	  loop invariant \forall integer k ; i <= k <= last ==> value <= a[k];
	  loop invariant \forall integer k ; beg <= k <= i    ==> a[k] == \at(a[k], Pre) ;
	  loop invariant Sorted(a, beg, last-1) ;
	  loop invariant i != last ==> \forall integer k; beg <= k <= last ==> a[k] <= a[last];
	  loop invariant i != last ==> Sorted(a, beg, last);
	  loop invariant a[last-1] <= value ==> Sorted(a, beg, last);
	  loop assigns i, a[beg .. last] ;
	  loop variant i ;
	 */

	while(i > beg && a[i-1] > value)
	{
		/*@ assert Sorted(a, beg, last-1);*/
		/*@ assert \forall integer k; beg <= k <= i-1 ==> a[k] <= a[i-1];*/
		a[i]= a[i-1];
		/*@ assert a[i-1] == a[i];*/
		/*@ assert \forall integer k; beg <= k <= i ==> a[k] <= a[i];*/
		/*@ assert Sorted(a, beg, last-1);*/
		/*@ assert Sorted(a, beg, last);*/
		/*@ assert \forall integer k; beg <= k <= last ==> a[k] <= a[last];*/
		--i;
	}

	/*@ assert Sorted(a, beg, last-1) ;*/
	/*@ assert i != last ==> Sorted(a, beg, last) ;*/
	/*@ assert i == last ==> a[last-1] <= a[last];*/
	/*@ assert Sorted(a, beg, last) ;*/
	/*@ assert \forall integer k ; beg <= k <= i-1 ==> a[k] <= value;*/
	a[i] = value;
	/*@ assert Sorted(a, beg, last) ;*/

	/*@ assert unchanged{Pre, Here}(a, beg, i-1) ;*/
	/*@ assert Permut{Pre, Here}(a, beg, i-1) ;*/
	// assert rotate_left{Pre, Here}(a, i, last) ; 
	/*@ assert Permut{Pre, Here}(a, i, last) ;*/
// 	
}


/*@ requires beg < end && \valid(a + (beg .. end-1));
  @ assigns a[beg .. end-1];
  @ ensures Sorted(a, beg, end-1);
  @ ensures Permut{Old, Post}(a, beg, end-1);
  @*/
void insertion_sort(int *a, size_t beg, size_t end)
{

	/*@ loop invariant beg + 1 <= i <= end;
	  @ loop invariant Sorted(a, beg, i-1);
	  @ loop invariant Permut{Pre, Here}(a, beg, end-1);
	  @ loop assigns a[beg .. end-1], i;
	  @ loop variant end-i;
	  @*/
	for (size_t i = beg + 1; i < end; ++i)
	{
		insert(a, beg, i);

		/*@ assert Permut{LoopCurrent, Here}(a, beg, i);*/
		/*@ assert unchanged{LoopCurrent, Here}(a, i+1, end-1);*/
		/*@ assert Permut{LoopCurrent, Here}(a, i+1, end-1);*/
		/*@ assert Permut{LoopCurrent, Here}(a, beg, end-1);*/
	}
}
// 
// 
// 
// 
