import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1730
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1731
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1732
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1733
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1734
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1735
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1736
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1737
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1738
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1739

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_173 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 173 + i)) (500 * (10 * 173 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1730
  by_cases h1 : i = 1
  · subst i
    exact chunk_1731
  by_cases h2 : i = 2
  · subst i
    exact chunk_1732
  by_cases h3 : i = 3
  · subst i
    exact chunk_1733
  by_cases h4 : i = 4
  · subst i
    exact chunk_1734
  by_cases h5 : i = 5
  · subst i
    exact chunk_1735
  by_cases h6 : i = 6
  · subst i
    exact chunk_1736
  by_cases h7 : i = 7
  · subst i
    exact chunk_1737
  by_cases h8 : i = 8
  · subst i
    exact chunk_1738
  by_cases h9 : i = 9
  · subst i
    exact chunk_1739
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
