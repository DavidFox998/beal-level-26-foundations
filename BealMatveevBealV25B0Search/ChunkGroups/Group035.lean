import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0350
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0351
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0352
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0353
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0354
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0355
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0356
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0357
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0358
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0359

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_035 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 35 + i)) (500 * (10 * 35 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0350
  by_cases h1 : i = 1
  · subst i
    exact chunk_0351
  by_cases h2 : i = 2
  · subst i
    exact chunk_0352
  by_cases h3 : i = 3
  · subst i
    exact chunk_0353
  by_cases h4 : i = 4
  · subst i
    exact chunk_0354
  by_cases h5 : i = 5
  · subst i
    exact chunk_0355
  by_cases h6 : i = 6
  · subst i
    exact chunk_0356
  by_cases h7 : i = 7
  · subst i
    exact chunk_0357
  by_cases h8 : i = 8
  · subst i
    exact chunk_0358
  by_cases h9 : i = 9
  · subst i
    exact chunk_0359
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
