<?php
// Laravel (overlays/laravel.json): the request object is the source; DB::raw and whereRaw are sinks; a bound parameter is not.  EXPECT: REFUTED, EARNED, REFUTED
use Illuminate\Support\Facades\DB;
class TopicController {
    public function index(Request $request) {
        $q = $request->input('q');
        $rows = DB::select("SELECT * FROM topics WHERE title LIKE '%" . $q . "%'");
        $rows = DB::table('topics')->whereRaw("title LIKE ?", ["%" . $q . "%"])->get();
        $rows = DB::table('topics')->orderByRaw("FIELD(id, " . request()->input('order') . ")")->get();
        return $rows;
    }
}
