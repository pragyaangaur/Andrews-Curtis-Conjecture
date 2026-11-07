import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 281 of the cap-17 certificate: slots 143872 .. 144383 -/
theorem chk_281 : chunkCheck 17 T stdSt 143872 512 = true := by decide +kernel

end Row17
