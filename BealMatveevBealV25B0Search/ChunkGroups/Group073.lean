import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0730
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0731
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0732
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0733
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0734
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0735
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0736
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0737
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0738
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0739

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_073 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 73 + i)) (500 * (10 * 73 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0730
  by_cases h1 : i = 1
  · subst i
    exact chunk_0731
  by_cases h2 : i = 2
  · subst i
    exact chunk_0732
  by_cases h3 : i = 3
  · subst i
    exact chunk_0733
  by_cases h4 : i = 4
  · subst i
    exact chunk_0734
  by_cases h5 : i = 5
  · subst i
    exact chunk_0735
  by_cases h6 : i = 6
  · subst i
    exact chunk_0736
  by_cases h7 : i = 7
  · subst i
    exact chunk_0737
  by_cases h8 : i = 8
  · subst i
    exact chunk_0738
  by_cases h9 : i = 9
  · subst i
    exact chunk_0739
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
