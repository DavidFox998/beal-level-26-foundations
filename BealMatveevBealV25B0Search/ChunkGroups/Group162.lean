import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1620
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1621
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1622
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1623
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1624
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1625
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1626
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1627
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1628
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1629

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_162 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 162 + i)) (500 * (10 * 162 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1620
  by_cases h1 : i = 1
  · subst i
    exact chunk_1621
  by_cases h2 : i = 2
  · subst i
    exact chunk_1622
  by_cases h3 : i = 3
  · subst i
    exact chunk_1623
  by_cases h4 : i = 4
  · subst i
    exact chunk_1624
  by_cases h5 : i = 5
  · subst i
    exact chunk_1625
  by_cases h6 : i = 6
  · subst i
    exact chunk_1626
  by_cases h7 : i = 7
  · subst i
    exact chunk_1627
  by_cases h8 : i = 8
  · subst i
    exact chunk_1628
  by_cases h9 : i = 9
  · subst i
    exact chunk_1629
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
