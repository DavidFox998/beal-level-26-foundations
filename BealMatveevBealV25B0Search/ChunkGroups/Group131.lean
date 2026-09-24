import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1310
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1311
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1312
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1313
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1314
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1315
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1316
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1317
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1318
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1319

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_131 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 131 + i)) (500 * (10 * 131 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1310
  by_cases h1 : i = 1
  · subst i
    exact chunk_1311
  by_cases h2 : i = 2
  · subst i
    exact chunk_1312
  by_cases h3 : i = 3
  · subst i
    exact chunk_1313
  by_cases h4 : i = 4
  · subst i
    exact chunk_1314
  by_cases h5 : i = 5
  · subst i
    exact chunk_1315
  by_cases h6 : i = 6
  · subst i
    exact chunk_1316
  by_cases h7 : i = 7
  · subst i
    exact chunk_1317
  by_cases h8 : i = 8
  · subst i
    exact chunk_1318
  by_cases h9 : i = 9
  · subst i
    exact chunk_1319
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
