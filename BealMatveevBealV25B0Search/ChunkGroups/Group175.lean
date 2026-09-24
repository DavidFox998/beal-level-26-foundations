import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1750
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1751
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1752
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1753
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1754
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1755
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1756
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1757
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1758
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1759

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_175 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 175 + i)) (500 * (10 * 175 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1750
  by_cases h1 : i = 1
  · subst i
    exact chunk_1751
  by_cases h2 : i = 2
  · subst i
    exact chunk_1752
  by_cases h3 : i = 3
  · subst i
    exact chunk_1753
  by_cases h4 : i = 4
  · subst i
    exact chunk_1754
  by_cases h5 : i = 5
  · subst i
    exact chunk_1755
  by_cases h6 : i = 6
  · subst i
    exact chunk_1756
  by_cases h7 : i = 7
  · subst i
    exact chunk_1757
  by_cases h8 : i = 8
  · subst i
    exact chunk_1758
  by_cases h9 : i = 9
  · subst i
    exact chunk_1759
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
