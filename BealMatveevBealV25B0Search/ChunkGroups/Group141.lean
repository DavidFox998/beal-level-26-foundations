import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1410
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1411
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1412
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1413
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1414
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1415
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1416
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1417
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1418
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1419

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_141 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 141 + i)) (500 * (10 * 141 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1410
  by_cases h1 : i = 1
  · subst i
    exact chunk_1411
  by_cases h2 : i = 2
  · subst i
    exact chunk_1412
  by_cases h3 : i = 3
  · subst i
    exact chunk_1413
  by_cases h4 : i = 4
  · subst i
    exact chunk_1414
  by_cases h5 : i = 5
  · subst i
    exact chunk_1415
  by_cases h6 : i = 6
  · subst i
    exact chunk_1416
  by_cases h7 : i = 7
  · subst i
    exact chunk_1417
  by_cases h8 : i = 8
  · subst i
    exact chunk_1418
  by_cases h9 : i = 9
  · subst i
    exact chunk_1419
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
