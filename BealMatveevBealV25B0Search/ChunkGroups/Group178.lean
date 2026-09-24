import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1780
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1781
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1782
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1783
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1784
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1785
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1786
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1787
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1788
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1789

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_178 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 178 + i)) (500 * (10 * 178 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1780
  by_cases h1 : i = 1
  · subst i
    exact chunk_1781
  by_cases h2 : i = 2
  · subst i
    exact chunk_1782
  by_cases h3 : i = 3
  · subst i
    exact chunk_1783
  by_cases h4 : i = 4
  · subst i
    exact chunk_1784
  by_cases h5 : i = 5
  · subst i
    exact chunk_1785
  by_cases h6 : i = 6
  · subst i
    exact chunk_1786
  by_cases h7 : i = 7
  · subst i
    exact chunk_1787
  by_cases h8 : i = 8
  · subst i
    exact chunk_1788
  by_cases h9 : i = 9
  · subst i
    exact chunk_1789
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
