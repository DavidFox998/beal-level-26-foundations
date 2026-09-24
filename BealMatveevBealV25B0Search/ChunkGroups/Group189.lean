import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1890
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1891
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1892
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1893
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1894
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1895
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1896
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1897
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1898
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1899

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_189 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 189 + i)) (500 * (10 * 189 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1890
  by_cases h1 : i = 1
  · subst i
    exact chunk_1891
  by_cases h2 : i = 2
  · subst i
    exact chunk_1892
  by_cases h3 : i = 3
  · subst i
    exact chunk_1893
  by_cases h4 : i = 4
  · subst i
    exact chunk_1894
  by_cases h5 : i = 5
  · subst i
    exact chunk_1895
  by_cases h6 : i = 6
  · subst i
    exact chunk_1896
  by_cases h7 : i = 7
  · subst i
    exact chunk_1897
  by_cases h8 : i = 8
  · subst i
    exact chunk_1898
  by_cases h9 : i = 9
  · subst i
    exact chunk_1899
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
