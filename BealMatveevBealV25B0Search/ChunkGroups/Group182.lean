import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1820
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1821
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1822
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1823
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1824
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1825
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1826
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1827
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1828
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1829

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_182 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 182 + i)) (500 * (10 * 182 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1820
  by_cases h1 : i = 1
  · subst i
    exact chunk_1821
  by_cases h2 : i = 2
  · subst i
    exact chunk_1822
  by_cases h3 : i = 3
  · subst i
    exact chunk_1823
  by_cases h4 : i = 4
  · subst i
    exact chunk_1824
  by_cases h5 : i = 5
  · subst i
    exact chunk_1825
  by_cases h6 : i = 6
  · subst i
    exact chunk_1826
  by_cases h7 : i = 7
  · subst i
    exact chunk_1827
  by_cases h8 : i = 8
  · subst i
    exact chunk_1828
  by_cases h9 : i = 9
  · subst i
    exact chunk_1829
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
