import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 73 of the cap-16 certificate: slots 74752 .. 75775 -/
theorem chk_73 : chunkCheck 16 T stdSt 74752 1024 = true := by decide +kernel

end Row16
