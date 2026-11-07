import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 59 of the cap-17 certificate: slots 30208 .. 30719 -/
theorem chk_59 : chunkCheck 17 T stdSt 30208 512 = true := by decide +kernel

end Row17
