import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1430
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1431
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1432
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1433
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1434
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1435
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1436
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1437
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1438
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1439

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_143 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 143 + i)) (500 * (10 * 143 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1430
  by_cases h1 : i = 1
  · subst i
    exact chunk_1431
  by_cases h2 : i = 2
  · subst i
    exact chunk_1432
  by_cases h3 : i = 3
  · subst i
    exact chunk_1433
  by_cases h4 : i = 4
  · subst i
    exact chunk_1434
  by_cases h5 : i = 5
  · subst i
    exact chunk_1435
  by_cases h6 : i = 6
  · subst i
    exact chunk_1436
  by_cases h7 : i = 7
  · subst i
    exact chunk_1437
  by_cases h8 : i = 8
  · subst i
    exact chunk_1438
  by_cases h9 : i = 9
  · subst i
    exact chunk_1439
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
