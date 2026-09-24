import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1370
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1371
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1372
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1373
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1374
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1375
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1376
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1377
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1378
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1379

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_137 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 137 + i)) (500 * (10 * 137 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1370
  by_cases h1 : i = 1
  · subst i
    exact chunk_1371
  by_cases h2 : i = 2
  · subst i
    exact chunk_1372
  by_cases h3 : i = 3
  · subst i
    exact chunk_1373
  by_cases h4 : i = 4
  · subst i
    exact chunk_1374
  by_cases h5 : i = 5
  · subst i
    exact chunk_1375
  by_cases h6 : i = 6
  · subst i
    exact chunk_1376
  by_cases h7 : i = 7
  · subst i
    exact chunk_1377
  by_cases h8 : i = 8
  · subst i
    exact chunk_1378
  by_cases h9 : i = 9
  · subst i
    exact chunk_1379
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
