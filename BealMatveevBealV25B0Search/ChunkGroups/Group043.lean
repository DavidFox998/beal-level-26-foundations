import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0430
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0431
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0432
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0433
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0434
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0435
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0436
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0437
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0438
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0439

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_043 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 43 + i)) (500 * (10 * 43 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0430
  by_cases h1 : i = 1
  · subst i
    exact chunk_0431
  by_cases h2 : i = 2
  · subst i
    exact chunk_0432
  by_cases h3 : i = 3
  · subst i
    exact chunk_0433
  by_cases h4 : i = 4
  · subst i
    exact chunk_0434
  by_cases h5 : i = 5
  · subst i
    exact chunk_0435
  by_cases h6 : i = 6
  · subst i
    exact chunk_0436
  by_cases h7 : i = 7
  · subst i
    exact chunk_0437
  by_cases h8 : i = 8
  · subst i
    exact chunk_0438
  by_cases h9 : i = 9
  · subst i
    exact chunk_0439
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
