import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0310
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0311
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0312
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0313
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0314
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0315
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0316
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0317
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0318
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0319

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_031 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 31 + i)) (500 * (10 * 31 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0310
  by_cases h1 : i = 1
  · subst i
    exact chunk_0311
  by_cases h2 : i = 2
  · subst i
    exact chunk_0312
  by_cases h3 : i = 3
  · subst i
    exact chunk_0313
  by_cases h4 : i = 4
  · subst i
    exact chunk_0314
  by_cases h5 : i = 5
  · subst i
    exact chunk_0315
  by_cases h6 : i = 6
  · subst i
    exact chunk_0316
  by_cases h7 : i = 7
  · subst i
    exact chunk_0317
  by_cases h8 : i = 8
  · subst i
    exact chunk_0318
  by_cases h9 : i = 9
  · subst i
    exact chunk_0319
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
