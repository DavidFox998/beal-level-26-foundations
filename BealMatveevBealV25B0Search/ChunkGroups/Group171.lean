import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1710
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1711
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1712
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1713
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1714
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1715
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1716
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1717
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1718
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1719

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_171 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 171 + i)) (500 * (10 * 171 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1710
  by_cases h1 : i = 1
  · subst i
    exact chunk_1711
  by_cases h2 : i = 2
  · subst i
    exact chunk_1712
  by_cases h3 : i = 3
  · subst i
    exact chunk_1713
  by_cases h4 : i = 4
  · subst i
    exact chunk_1714
  by_cases h5 : i = 5
  · subst i
    exact chunk_1715
  by_cases h6 : i = 6
  · subst i
    exact chunk_1716
  by_cases h7 : i = 7
  · subst i
    exact chunk_1717
  by_cases h8 : i = 8
  · subst i
    exact chunk_1718
  by_cases h9 : i = 9
  · subst i
    exact chunk_1719
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
