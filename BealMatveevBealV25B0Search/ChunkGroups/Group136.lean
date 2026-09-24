import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1360
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1361
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1362
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1363
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1364
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1365
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1366
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1367
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1368
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1369

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_136 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 136 + i)) (500 * (10 * 136 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1360
  by_cases h1 : i = 1
  · subst i
    exact chunk_1361
  by_cases h2 : i = 2
  · subst i
    exact chunk_1362
  by_cases h3 : i = 3
  · subst i
    exact chunk_1363
  by_cases h4 : i = 4
  · subst i
    exact chunk_1364
  by_cases h5 : i = 5
  · subst i
    exact chunk_1365
  by_cases h6 : i = 6
  · subst i
    exact chunk_1366
  by_cases h7 : i = 7
  · subst i
    exact chunk_1367
  by_cases h8 : i = 8
  · subst i
    exact chunk_1368
  by_cases h9 : i = 9
  · subst i
    exact chunk_1369
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
