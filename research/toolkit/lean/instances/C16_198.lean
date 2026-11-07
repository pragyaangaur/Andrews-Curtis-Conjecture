import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 198 of the cap-16 certificate: slots 202752 .. 203775 -/
theorem chk_198 : chunkCheck 16 T stdSt 202752 1024 = true := by decide +kernel

end Row16
