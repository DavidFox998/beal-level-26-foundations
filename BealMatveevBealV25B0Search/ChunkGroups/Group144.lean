import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1440
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1441
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1442
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1443
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1444
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1445
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1446
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1447
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1448
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1449

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_144 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 144 + i)) (500 * (10 * 144 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1440
  by_cases h1 : i = 1
  · subst i
    exact chunk_1441
  by_cases h2 : i = 2
  · subst i
    exact chunk_1442
  by_cases h3 : i = 3
  · subst i
    exact chunk_1443
  by_cases h4 : i = 4
  · subst i
    exact chunk_1444
  by_cases h5 : i = 5
  · subst i
    exact chunk_1445
  by_cases h6 : i = 6
  · subst i
    exact chunk_1446
  by_cases h7 : i = 7
  · subst i
    exact chunk_1447
  by_cases h8 : i = 8
  · subst i
    exact chunk_1448
  by_cases h9 : i = 9
  · subst i
    exact chunk_1449
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
