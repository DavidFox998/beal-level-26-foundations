import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0340
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0341
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0342
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0343
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0344
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0345
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0346
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0347
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0348
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0349

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_034 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 34 + i)) (500 * (10 * 34 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0340
  by_cases h1 : i = 1
  · subst i
    exact chunk_0341
  by_cases h2 : i = 2
  · subst i
    exact chunk_0342
  by_cases h3 : i = 3
  · subst i
    exact chunk_0343
  by_cases h4 : i = 4
  · subst i
    exact chunk_0344
  by_cases h5 : i = 5
  · subst i
    exact chunk_0345
  by_cases h6 : i = 6
  · subst i
    exact chunk_0346
  by_cases h7 : i = 7
  · subst i
    exact chunk_0347
  by_cases h8 : i = 8
  · subst i
    exact chunk_0348
  by_cases h9 : i = 9
  · subst i
    exact chunk_0349
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
