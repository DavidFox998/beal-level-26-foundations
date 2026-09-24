import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1770
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1771
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1772
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1773
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1774
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1775
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1776
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1777
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1778
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1779

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_177 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 177 + i)) (500 * (10 * 177 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1770
  by_cases h1 : i = 1
  · subst i
    exact chunk_1771
  by_cases h2 : i = 2
  · subst i
    exact chunk_1772
  by_cases h3 : i = 3
  · subst i
    exact chunk_1773
  by_cases h4 : i = 4
  · subst i
    exact chunk_1774
  by_cases h5 : i = 5
  · subst i
    exact chunk_1775
  by_cases h6 : i = 6
  · subst i
    exact chunk_1776
  by_cases h7 : i = 7
  · subst i
    exact chunk_1777
  by_cases h8 : i = 8
  · subst i
    exact chunk_1778
  by_cases h9 : i = 9
  · subst i
    exact chunk_1779
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
