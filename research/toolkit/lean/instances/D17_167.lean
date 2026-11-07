import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 167 of the cap-17 certificate: slots 85504 .. 86015 -/
theorem chk_167 : chunkCheck 17 T stdSt 85504 512 = true := by decide +kernel

end Row17
