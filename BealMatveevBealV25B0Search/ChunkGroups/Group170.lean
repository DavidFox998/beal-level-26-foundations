import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1700
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1701
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1702
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1703
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1704
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1705
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1706
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1707
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1708
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1709

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_170 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 170 + i)) (500 * (10 * 170 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1700
  by_cases h1 : i = 1
  · subst i
    exact chunk_1701
  by_cases h2 : i = 2
  · subst i
    exact chunk_1702
  by_cases h3 : i = 3
  · subst i
    exact chunk_1703
  by_cases h4 : i = 4
  · subst i
    exact chunk_1704
  by_cases h5 : i = 5
  · subst i
    exact chunk_1705
  by_cases h6 : i = 6
  · subst i
    exact chunk_1706
  by_cases h7 : i = 7
  · subst i
    exact chunk_1707
  by_cases h8 : i = 8
  · subst i
    exact chunk_1708
  by_cases h9 : i = 9
  · subst i
    exact chunk_1709
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
