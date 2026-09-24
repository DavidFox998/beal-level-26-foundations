import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0660
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0661
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0662
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0663
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0664
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0665
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0666
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0667
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0668
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0669

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_066 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 66 + i)) (500 * (10 * 66 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0660
  by_cases h1 : i = 1
  · subst i
    exact chunk_0661
  by_cases h2 : i = 2
  · subst i
    exact chunk_0662
  by_cases h3 : i = 3
  · subst i
    exact chunk_0663
  by_cases h4 : i = 4
  · subst i
    exact chunk_0664
  by_cases h5 : i = 5
  · subst i
    exact chunk_0665
  by_cases h6 : i = 6
  · subst i
    exact chunk_0666
  by_cases h7 : i = 7
  · subst i
    exact chunk_0667
  by_cases h8 : i = 8
  · subst i
    exact chunk_0668
  by_cases h9 : i = 9
  · subst i
    exact chunk_0669
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
