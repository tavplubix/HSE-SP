/// Доказывается солверами Z3 и CVC4 (каждым по-отдельности)
/// Последовательность действий и настройки:
///     time limit = 1s, memory limit = 4000Mb
///     sort_c, split, split
///     Z3/CVC4
///     auto level 1
///     time limit = 30s
///     auto level 1
/// Версии: Z3 4.4.1, CVC4 1.5 (из репозитория Ubuntu 18.04)


/// Идея доказательства:
/// 1. Отсортированность массива. 
///    Сортировка Шелла является более общим случаем сортировки вставками:
///    сначала вставками сортируются некоторые подмассивы, а на последней итерации
///    внешнего цикла происходит досортировка (тоже вставками) всего массива.
///    Вообще говоря, внешний цикл и сортировка подмассивов нужны только в целях оптимизации,
///    и не влияют на корректность: массив в любом случае будет досортирован
///    на послдней итерации (когда gap == 1). Поэтому достаточно доказать, что массив
///    будет отсортирован при gap == 1, и что такое значение gap будет достигнуто.
/// 2. Результат является перестановкой исходного массива.
///    Мы определяем перестановку массива как последовательность транспозиций (операций Swap),
///    однако в данной реализации сортировки Шелла происходит циклический сдвиг подпоследовательности,
///    а не попарный обмен элементов массива. Конечно, циклический сдвиг можно представить
///    как последовательность Swap, но это крайне затруднительно сделать для данного кода,
///    т.к. сдвиг происходящий во внутреннем цикле фактически не является последовательностью Swap,
///    а инвариант "массив является перестановкой исходного" нарушается внутри этого цикла и
///    восстанавливается только после завершения цикла и присваивания arr[j] = tmp.
///    Поэтому, будем использовать вспомогательный ghost массив, который изначально равен исходному,
///    но сдвигается с помощью последовательности честных Swap. Это позволяет (относительно) легко
///    доказать, что вспомогательный массив останется перестановкой исходного массива.
///    Также доказав, что после (слегка разного) циклического сдвига вспомогательный и основной массивы
///    остаются равны, мы получим, что основной массив тоже является перестановкой исходного.


/*@ predicate Sorted{L}(int *t, integer a, integer b) =
  @     \forall integer i, j; a <= i <= j <= b ==> t[i] <= t[j];
  @*/

/*@ predicate Swap{L1,L2}(int *a, int *b, integer i, integer j) =
  @     \at(a[i],L1) == \at(b[j],L2) &&
  @     \at(a[j],L1) == \at(b[i],L2) &&
  @     \forall integer k; k != i && k != j ==> \at(a[k],L1) == \at(b[k],L2);
  @*/


/// Предикат поэлементного равенства двух массивов: "массив `b` в состоянии `LB` поэлементно равен массиву `a` в состоянии `LA`"
/*@ predicate ArrayEquals{LA,LB}(int *a, int *b, integer l, integer r) = 
  @     \forall integer i; l <= i <= r ==> \at(a[i], LA) == \at(b[i], LB);
  @*/


/// Модифицированный предикат перестановок: "массив `b` в состоянии `L2` является перестановкой массива `a` в состоянии `L1`"
/*@ inductive Permut{L1,L2}(int *a, int *b, integer l, integer h) {
  @     case Permut_refl_equal{LA,LB}:
  @         \forall int *a, int *b, integer l, h;
  @         ArrayEquals{LA,LB}(a, b, l, h) ==> Permut{LA,LB}(a, b, l, h);
  @     case Permut_sym{L1,L2}:
  @         \forall int *a, int *b, integer l, h;
  @         Permut{L1,L2}(a, b, l, h) ==> Permut{L2,L1}(b, a, l, h);
  @     case Permut_trans{L1,L2,L3}:
  @         \forall int *a, int *b, int *c, integer l, h;
  @         Permut{L1,L2}(a, b, l, h) && Permut{L2,L3}(b, c, l, h) ==> Permut{L1,L3}(a, c, l, h);
  @     case Permut_swap{L1,L2}:
  @         \forall int *a, int *b, integer l, h, i, j;
  @         l <= i <= h && l <= j <= h && Swap{L1,L2}(a, b, i, j) ==> Permut{L1,L2}(a, b, l, h);
  @ }
  @*/

/*@ lemma EqualArraysPermutations{L1,L2}:
  @   \forall int *a, int *b, integer r;
  @       ArrayEquals{L1,L1}(a, b, 0, r) && Permut{L1,L2}(b, b, 0, r) && ArrayEquals{L2,L2}(b, a, 0, r) ==> Permut{L1,L2}(a, a, 0, r);
  @*/

/* lemma SortedAppend:
      \forall int *a, integer i;
          i > 0 && Sorted(a, 0, i-1) && a[i-1] <= a[i] ==> Sorted(a, 0, i);
  */


/// Чтобы не выделять динамически память для вспомогательного массива 
/// (который не нужен и используется только в доказательстве) внутри функции,
/// выделим достаточно памяти здесь.
#define INT_MAX 2147483647
//@ ghost int ghost_array_dirty_hack[INT_MAX];


/*@ requires n >= 0;
  @ requires \valid(arr + (0 .. n-1));
  @
  @ assigns arr[0 .. n-1];
  @ assigns ghost_array_dirty_hack[0 .. n-1];
  @ 
  @ ensures Permut{Old,Here}(arr, arr, 0, n-1);
  @ ensures Sorted(arr, 0, n-1);
  @*/

void shell_lr(int *arr, int n) { 

    /*@ ghost
            int *arr2 = &ghost_array_dirty_hack[0];
            /@ assert \valid(arr2 + (0 .. n-1));
            @/
            /@ loop invariant ArrayEquals{Here,Here}(arr, arr2, 0, k-1);
               loop invariant 0 <= k <= n;
               loop assigns k, arr2[0 .. n-1];
               loop variant n - k;
            @/
            for (int k = 0; k < n; ++k) {
                //@ assert 0 <= k;
                //@ assert k <= n-1;
                arr2[k] = arr[k];
            }
    */

    int i, j, tmp, gap;

    /*@ loop invariant 0 <= gap <= n/2 <= n;
      @
      @ loop invariant ArrayEquals{Here,Here}(arr, arr2, 0, n-1);
      @ loop invariant Permut{Pre,Here}(arr, arr, 0, n-1);
      @
      @ loop invariant gap == 0 ==> Sorted(arr, 0, n-1);
      @
      @ loop assigns gap, i, j, tmp, arr[0 .. n-1], arr2[0 .. n-1];
      @ loop variant gap;
      @*/  
    for (gap = n / 2; gap > 0; gap /= 2) {
	//@ assert 0 < gap < n;

        //@ assert ArrayEquals{Here,Here}(arr, arr2, 0, n-1);

        /*@ loop invariant 1 <= i <= n;
	  @
	  @ loop invariant Permut{Pre,Here}(arr, arr, 0, n-1);
	  @ loop invariant ArrayEquals{Here,Here}(arr, arr2, 0, n-1);
	  @
	  @ loop invariant gap == 1 ==> Sorted(arr, 0, i-1);
	  @
	  @ loop assigns i, j, tmp, arr[0 .. n-1], arr2[0 .. n-1];
	  @ loop variant n-i;
	  @*/   
	for (i = gap; i < n; ++i) { 
	    //@ assert i > 0;
            //@ assert i < n;
            tmp = arr[i];

            //@ ghost int tmp2 = tmp;
            //@ assert ArrayEquals{Here,Here}(arr, arr2, 0, n-1);
	    //@ assert Permut{LoopCurrent,Here}(arr2, arr2, 0, n-1);
            //@ assert Permut{LoopCurrent,Here}(arr, arr, 0, n-1);

	    /*@ loop invariant 0 <= j <= i;
	      @ 
	      @ loop invariant Permut{LoopEntry,Here}(arr2, arr2, 0, n-1);
	      @ loop invariant arr2[j] == tmp2;
	      @ loop invariant tmp2 == tmp;
	      @ loop invariant arr2[j] == tmp2 ==> arr2[j] == tmp;
              @ loop invariant ArrayEquals{Here,Here}(arr, arr2, 0, j-1) && ArrayEquals{Here,Here}(arr, arr2, j+1, n-1);
	      @
	      @ loop invariant gap == 1 ==> \forall integer k ; j <= k <= i ==> tmp <= arr[k];
	      @ loop invariant gap == 1 ==> \forall integer k ; 0 <= k <= j ==> arr[k] == \at(arr[k], LoopEntry);
	      @ loop invariant gap == 1 ==> Sorted(arr, 0, i-1);
	      @ loop invariant gap == 1 ==> j != i ==> \forall integer k; 0 <= k <= i ==> arr[k] <= arr[i];
	      @ loop invariant gap == 1 ==> j != i ==> Sorted(arr, 0, i);
	      @ loop invariant gap == 1 ==> arr[i-1] <= tmp ==> Sorted(arr, 0, i);
              @
	      @ loop assigns j, arr[0 .. i], arr2[0 .. i], tmp2;
	      @ loop variant j;
	      @*/ 
            for (j = i; j >= gap && arr[j - gap] > tmp; j -= gap) { 
                //@ assert j >= gap;
		//@ assert 0 < j;
		//@ assert j - gap >= 0;
		//@ assert j < n;
		//@ assert j - gap < n;

	        //@ ghost tmp2 = arr2[j]; 
		//@ ghost arr2[j] = arr2[j - gap];
		//@ ghost arr2[j - gap] = tmp2;

                //@ assert gap == 1 ==> Sorted(arr, 0, i-1);
		//@ assert gap == 1 ==> \forall integer k; 0 <= k <= j-1 ==> arr[k] <= arr[j-1];

                arr[j] = arr[j - gap];
		//@ assert gap == 1 ==> arr[j-1] == arr[j];
                //@ assert gap == 1 ==> \forall integer k; 0 <= k <= j ==> arr[k] <= arr[j];
                //@ assert gap == 1 ==> Sorted(arr, 0, i-1);
                //@ assert gap == 1 ==> \forall integer k; 0 <= k <= i ==> arr[k] <= arr[i];

		//@ assert arr[j] == arr2[j];
		//@ assert ArrayEquals{Here,Here}(arr, arr2, j+1, n-1);

                //@ assert Swap{LoopCurrent,Here}(arr2, arr2, j, j - gap);
		//@ assert Permut{LoopCurrent,Here}(arr2, arr2, 0, n-1);
            }
	    //@ assert 0 <= j;
	    //@ assert j < n;
	    
	    //@ assert Permut{LoopCurrent,Here}(arr2, arr2, 0, n-1);
	    //@ assert ArrayEquals{Here,Here}(arr, arr2, 0, j-1) && ArrayEquals{Here,Here}(arr, arr2, j+1, n-1);
	    //@ assert tmp2 == tmp;
	    //@ assert arr2[j] == tmp;
	    //@ assert gap == 1 ==> Sorted(arr, 0, i);
            arr[j] = tmp;
	    //@ assert gap == 1 ==> j >= 1 ==>  arr[j-1] <= arr[j];
	    //@ assert gap == 1 ==> \forall integer k; 0 <= k <= j ==> arr[k] <= arr[j];
            //@ assert gap == 1 ==> \forall integer k; j <= k <= i ==> arr[j] <= arr[k];
	    //@ assert gap == 1 ==> Sorted(arr, 0, i-1);
	    //@ assert gap == 1 ==> Sorted(arr, 0, i);

	    //@ assert arr[j] == arr2[j];

	    //@ assert ArrayEquals{LoopCurrent,LoopCurrent}(arr2, arr, 0, n-1);
	    //@ assert Permut{LoopCurrent,Here}(arr2, arr2, 0, n-1);
	    //@ assert ArrayEquals{Here,Here}(arr2, arr, 0, n-1);
	    
	    //@ assert Permut{LoopCurrent,Here}(arr, arr, 0, n-1);
	    //@ assert Permut{LoopEntry,Here}(arr, arr, 0, n-1);
	    //@ assert Permut{Pre,Here}(arr, arr, 0, n-1);

	    //@ assert gap == 1 ==> Sorted(arr, 0, i);
        }
        //@ assert gap == 1 ==> Sorted(arr, 0, n-1);
    } 
    //@ assert gap == 0;
}


