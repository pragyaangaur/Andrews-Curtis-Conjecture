import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 238 of the cap-16 certificate: slots 243712 .. 244735 -/
theorem chk_238 : chunkCheck 16 T stdSt 243712 1024 = true := by decide +kernel

end Row16
