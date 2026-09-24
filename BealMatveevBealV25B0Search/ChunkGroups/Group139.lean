import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1390
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1391
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1392
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1393
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1394
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1395
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1396
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1397
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1398
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1399

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_139 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 139 + i)) (500 * (10 * 139 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1390
  by_cases h1 : i = 1
  · subst i
    exact chunk_1391
  by_cases h2 : i = 2
  · subst i
    exact chunk_1392
  by_cases h3 : i = 3
  · subst i
    exact chunk_1393
  by_cases h4 : i = 4
  · subst i
    exact chunk_1394
  by_cases h5 : i = 5
  · subst i
    exact chunk_1395
  by_cases h6 : i = 6
  · subst i
    exact chunk_1396
  by_cases h7 : i = 7
  · subst i
    exact chunk_1397
  by_cases h8 : i = 8
  · subst i
    exact chunk_1398
  by_cases h9 : i = 9
  · subst i
    exact chunk_1399
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
