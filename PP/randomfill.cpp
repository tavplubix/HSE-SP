#include <cstdint>


void randomfill(uint64_t *out, size_t n, uint64_t x, uint64_t a, uint64_t c)
{
	constexpr size_t unroll_iters = 16;
	size_t unrolled_n = (n / unroll_iters) * unroll_iters;

	uint64_t aa[unroll_iters];
	uint64_t cc[unroll_iters];
	aa[0] = a;
	cc[0] = c;
	for (size_t i = 1; i < unroll_iters; ++i)
	{
		aa[i] = aa[i-1] * a;
		cc[i] = cc[i-1] + c * aa[i-1];
	}

	const auto max_out = out + unrolled_n;

	while (out != max_out)
	{
		// x_{i+k} = a^k x_i + c(a^0 + ... + a^{k-1})
		#pragma unroll
		for (size_t i = 0; i < unroll_iters; ++i)
			out[i] = x * aa[i] + cc[i];
		x = out[unroll_iters - 1];
		out += unroll_iters;
	}

	for (size_t i = 0; i < n - unrolled_n; ++i)
	{
		x = x * a + c;
                out[i] = x;
	}
}


