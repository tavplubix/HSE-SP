#include <cstdlib>
#include <cstdint>
#include <vector>

#include <unistd.h>

#if !defined(likely)
#    define likely(x)   (__builtin_expect(!!(x), 1))
#endif
#if !defined(unlikely)
#    define unlikely(x) (__builtin_expect(!!(x), 0))
#endif


struct Entry
{
	struct Entry *next;
	long payload;
};


struct PageSizeInfo
{
	PageSizeInfo() 
		: page_size(sysconf(_SC_PAGESIZE))
	{
		pow2 = 1;
		while (pow2 < 64)
		{
			if (page_size == (1ULL << pow2))
				return;
			++pow2;
		}

		pow2 = 0;
	}

	inline bool is_same_page(void * p1, void * p2)
	{
		intptr_t intp1 = reinterpret_cast<intptr_t>(p1);
		intptr_t intp2 = reinterpret_cast<intptr_t>(p2);
		if (likely(pow2))
			return (intp1 ^ intp2) < page_size;
		// Деление слишком медленное, но его можно оптимизировать (по сути мы делим на константу).
		// Но это не очень нужно, где вы видели такие страницы?
		return intp1 / page_size == intp2 / page_size;
	}

	uint64_t page_size;
	uint8_t pow2;
};

// Санитайзеры боятся чёрной магии, которую использует функция (и правильно делают).
// С MSan должно работать нормально, т.к. мы не используем неинициализированную память,
// даже если прочитали её.
__attribute__((__no_sanitize__("address")))
__attribute__((__no_sanitize__("thread")))
__attribute__((__no_sanitize__("undefined")))
long listsum(struct Entry *e)
{
	static PageSizeInfo info;

	long sum = 0;
	
	while (e)
	{
		// Итак, нам известно, что в большинстве случаев узлы списка
		// расположены в памяти последовательно. Не очень понятно, как
		// использовать это знание для улучшения instruction-level parallelism,
		// ведь для этого нам нужно развернуть цикл и избавиться от зависимостей по данным
		// внутри итерации, а при проходе списка следеющая итерация принципиально
		// зависит от предыдущей, а ещё куча разыменовываний указателей...
		// Хотя подождите...
		
		constexpr size_t batch_size = 16;

		// Представим, что список действительно является массивом,
		// и будем работать с ним как с массивом, лол.

		// Массив влезает в одну страницу => не будет page fault => не будет segmentation fault (лол)
		// Мы ничего не записываем в эту память, так что не испортим чужие данные.
		// Да, мы можем прочитать какой-то мусор вместо элементов списка. 
		// Проверим это, и просто не будем использовать этот мусор.
		if (likely(info.is_same_page(e, e + batch_size)))
		{
			long s = 0;
			//size_t count = 0;
			intptr_t bad = 0;
			#pragma unroll
			for (size_t i = 0; i < batch_size; ++i)
			{
				s += e[i].payload;
				//if (e + i + 1 == e[i].next)
				//	++count;
				
				// Эта конструкция работает немного быстрее, чем закоментированный код.
				// Почему она вообще работает? Если адреса не равны, то в резутьтате xor 
				// получатся ненулевые биты, которые останутся в переменной bad.
				bad |= reinterpret_cast<intptr_t>(e + i + 1) ^ reinterpret_cast<intptr_t>(e[i].next);
			}

			//if (likely(count == batch_size))
                	if (likely(!bad))
			{
                        	// Нам повезло: все batch_size узлов списка лежали в памяти последовательно
                        	// и на одной странице
                        	sum += s;
                        	e = e[batch_size - 1].next;
                	}
               		else
                	{
                        	// Что-то пошло не так: посчитаем элемент честно
                        	// и будем надеяться, что следующие элементы лежат в памяти последовательно.
                        	sum += e->payload;
                        	e = e->next;
                	}
		}
		else
		{
			// Мы близко к концу страницы: посчитаем последние элементы честно.
			// Если этого не сделать, то на каждой итерации мы будем сновa пытаться считать быстро, но не сможем.
			intptr_t intp = reinterpret_cast<intptr_t>(e);
			intptr_t page_beg = info.pow2 ? ((intp >> info.pow2) << info.pow2) : (intp / info.page_size) * info.page_size;
			size_t max_elems = 1 + (page_beg + info.page_size - intp) / sizeof(Entry);
			
			for (; e && max_elems--; e = e->next)
                		sum += e->payload;
		}
	}

	return sum;
}

long listsum_basic(struct Entry *e)
{
	long sum = 0;
	for (; e; e = e->next)
                sum += e->payload;
        return sum;
}

constexpr size_t N = 1023;
constexpr size_t repeats = 1000 * 1000;

Entry data3[N];
Entry data0[N];

void fill_data(Entry * data, size_t & n)
{
	for (size_t i = 0; i < N; ++i)
        {
                data[i].payload = ++n;
                data[i].next = data + i + 1;
        }
}

int main(int argc, char ** argv)
{
	Entry * data1 = (Entry *)malloc(N * sizeof(Entry));
	std::vector<Entry> data2_vec;
	data2_vec.resize(N);
	Entry * data2 = data2_vec.data();


	size_t n = 0;
	fill_data(data0, n);
	data0[N-1].next = data1;
	fill_data(data1, n);
        data1[N-1].next = data2;
	fill_data(data2, n);
        data2[N-1].next = data3;
	fill_data(data3, n);
	data3[N-1].next = nullptr;

	uint64_t s = 0;

	for (size_t i = 0; i < repeats; ++i)
		s += listsum(data0);

	free(data1);
	uint64_t expected = repeats * n * (n + 1) / 2;
	return s == repeats;
}

