import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1720
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1721
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1722
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1723
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1724
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1725
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1726
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1727
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1728
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1729

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_172 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 172 + i)) (500 * (10 * 172 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1720
  by_cases h1 : i = 1
  · subst i
    exact chunk_1721
  by_cases h2 : i = 2
  · subst i
    exact chunk_1722
  by_cases h3 : i = 3
  · subst i
    exact chunk_1723
  by_cases h4 : i = 4
  · subst i
    exact chunk_1724
  by_cases h5 : i = 5
  · subst i
    exact chunk_1725
  by_cases h6 : i = 6
  · subst i
    exact chunk_1726
  by_cases h7 : i = 7
  · subst i
    exact chunk_1727
  by_cases h8 : i = 8
  · subst i
    exact chunk_1728
  by_cases h9 : i = 9
  · subst i
    exact chunk_1729
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
