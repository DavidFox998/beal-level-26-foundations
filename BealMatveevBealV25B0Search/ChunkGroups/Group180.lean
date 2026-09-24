import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1800
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1801
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1802
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1803
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1804
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1805
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1806
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1807
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1808
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1809

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_180 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 180 + i)) (500 * (10 * 180 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1800
  by_cases h1 : i = 1
  · subst i
    exact chunk_1801
  by_cases h2 : i = 2
  · subst i
    exact chunk_1802
  by_cases h3 : i = 3
  · subst i
    exact chunk_1803
  by_cases h4 : i = 4
  · subst i
    exact chunk_1804
  by_cases h5 : i = 5
  · subst i
    exact chunk_1805
  by_cases h6 : i = 6
  · subst i
    exact chunk_1806
  by_cases h7 : i = 7
  · subst i
    exact chunk_1807
  by_cases h8 : i = 8
  · subst i
    exact chunk_1808
  by_cases h9 : i = 9
  · subst i
    exact chunk_1809
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
