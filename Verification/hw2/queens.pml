// rm -f a.out pan.* *.trail && spin -a queens.pml && clang-10 pan.c && ./a.out && spin -t queens.pml

#define N 8    // размер доски

active proctype main() {

  bit row_attacked[N] = 0;   // 1 если кто-то уже бьёт строку 
  bit diag1_attacked[N * 2 - 1] = 0;    // 1 если кто-то уже бьёт диагональ row + col = const
  bit diag2_attacked[N * 2 - 1] = 0;    // 1 если кто-то уже бьёт диагональ row - col = const

  bit solved = 1;    // 1 если выполняется условие, что все ферзи не бьют друг друга

  byte row;
  byte col;

  for (col : 0 .. (N-1)) {    // ставим по одному ферзю в каждый столбец
    select(row : 0 .. (N-1));    // выбираем для него случайную строку
    printf("queen at col=%d, row=%d\n", col, row);
    
    // инвариант: условие выполняется, если оно выполнялось раньше, и нового ферзя никто не бьёт
    solved = solved == 1 && row_attacked[row] == 0 && diag1_attacked[row + col] == 0 && diag2_attacked[row - col + N - 1] == 0;
  
    // если инвариант нарушился - сразу выходим из цикла, если нет - продолжаем
    // (можно обойтись без этой конструкции, но с ней контрпример находится сильно быстрее) 
    if
      :: solved == 0 -> break;
      :: solved == 1 -> skip;
    fi

    // отметим строку и диагонали, которые бьёт новый ферзь
    row_attacked[row] = 1;
    diag1_attacked[row + col] = 1;
    diag2_attacked[row - col + N - 1] = 1;
  }

  // предположим, что при любых исполнениях условие не выполняется, чтобы получить контрпример с решением
  assert(solved == 0);
}

