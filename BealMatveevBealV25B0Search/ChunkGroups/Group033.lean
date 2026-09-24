import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0330
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0331
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0332
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0333
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0334
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0335
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0336
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0337
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0338
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0339

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_033 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 33 + i)) (500 * (10 * 33 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0330
  by_cases h1 : i = 1
  · subst i
    exact chunk_0331
  by_cases h2 : i = 2
  · subst i
    exact chunk_0332
  by_cases h3 : i = 3
  · subst i
    exact chunk_0333
  by_cases h4 : i = 4
  · subst i
    exact chunk_0334
  by_cases h5 : i = 5
  · subst i
    exact chunk_0335
  by_cases h6 : i = 6
  · subst i
    exact chunk_0336
  by_cases h7 : i = 7
  · subst i
    exact chunk_0337
  by_cases h8 : i = 8
  · subst i
    exact chunk_0338
  by_cases h9 : i = 9
  · subst i
    exact chunk_0339
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
