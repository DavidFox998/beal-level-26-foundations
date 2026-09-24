import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0280
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0281
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0282
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0283
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0284
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0285
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0286
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0287
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0288
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0289

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_028 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 28 + i)) (500 * (10 * 28 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0280
  by_cases h1 : i = 1
  · subst i
    exact chunk_0281
  by_cases h2 : i = 2
  · subst i
    exact chunk_0282
  by_cases h3 : i = 3
  · subst i
    exact chunk_0283
  by_cases h4 : i = 4
  · subst i
    exact chunk_0284
  by_cases h5 : i = 5
  · subst i
    exact chunk_0285
  by_cases h6 : i = 6
  · subst i
    exact chunk_0286
  by_cases h7 : i = 7
  · subst i
    exact chunk_0287
  by_cases h8 : i = 8
  · subst i
    exact chunk_0288
  by_cases h9 : i = 9
  · subst i
    exact chunk_0289
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
