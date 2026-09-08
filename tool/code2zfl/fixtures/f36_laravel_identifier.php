<?php
// Laravel binds VALUES, never column names: orderBy($request->input(...)) is an injection; a whitelisted column is not; a bound value is not a sink.  EXPECT: REFUTED, EARNED, EARNED
use Illuminate\Support\Facades\DB;
class TopicController {
    public function index(Request $request) {
        $sort = $request->input('sort');
        $a = DB::table('topics')->orderBy($sort)->get();
        if (in_array($sort, ['title', 'created_at', 'votes'])) {
            $b = DB::table('topics')->orderBy($sort)->get();
        }
        $c = DB::table('topics')->where('title', $request->input('q'))->get();
        return [$a, $b, $c];
    }
}
