import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1760
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1761
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1762
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1763
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1764
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1765
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1766
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1767
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1768
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1769

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_176 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 176 + i)) (500 * (10 * 176 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1760
  by_cases h1 : i = 1
  · subst i
    exact chunk_1761
  by_cases h2 : i = 2
  · subst i
    exact chunk_1762
  by_cases h3 : i = 3
  · subst i
    exact chunk_1763
  by_cases h4 : i = 4
  · subst i
    exact chunk_1764
  by_cases h5 : i = 5
  · subst i
    exact chunk_1765
  by_cases h6 : i = 6
  · subst i
    exact chunk_1766
  by_cases h7 : i = 7
  · subst i
    exact chunk_1767
  by_cases h8 : i = 8
  · subst i
    exact chunk_1768
  by_cases h9 : i = 9
  · subst i
    exact chunk_1769
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
