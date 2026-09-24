import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1570
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1571
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1572
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1573
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1574
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1575
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1576
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1577
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1578
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1579

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_157 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 157 + i)) (500 * (10 * 157 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1570
  by_cases h1 : i = 1
  · subst i
    exact chunk_1571
  by_cases h2 : i = 2
  · subst i
    exact chunk_1572
  by_cases h3 : i = 3
  · subst i
    exact chunk_1573
  by_cases h4 : i = 4
  · subst i
    exact chunk_1574
  by_cases h5 : i = 5
  · subst i
    exact chunk_1575
  by_cases h6 : i = 6
  · subst i
    exact chunk_1576
  by_cases h7 : i = 7
  · subst i
    exact chunk_1577
  by_cases h8 : i = 8
  · subst i
    exact chunk_1578
  by_cases h9 : i = 9
  · subst i
    exact chunk_1579
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
