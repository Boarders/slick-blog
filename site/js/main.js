function switchTheme(){
    var button = document.getElementById("theme-button");
    var html = document.getElementsByTagName("html")[0];
    html.classList.toggle("dark");

    if(button.innerHTML == "DAY"){
        button.innerHTML = "NIGHT";
        // Expire in two months
        setCookie("theme", "night", 60*24*60*60*1000);
    } else {
        button.innerHTML = "DAY";
        // Expire in two months
        setCookie("theme", "day", 60*24*60*60*1000);
    }
    return;
}

function setCookie(cname,cvalue,extime)
{
    var d = new Date();
    d.setTime(d.getTime()+(extime));
    var expires = "expires="+d.toGMTString();
    document.cookie = cname + "=" + cvalue + ";" + expires + ";" + "path=/"; 
}

function getCookie(cname)
{
    var name = cname + "=";
    var ca = document.cookie.split(';');
    for(var i=0; i<ca.length; i++)
    {
        var c = ca[i].trim();
        if (c.indexOf(name)===0) return c.substring(name.length,c.length);
    }
    return "";
}

// Switch theme if cookie is set
if (getCookie('theme')=='night') {
    switchTheme();
}

// Switch theme if button is clicked.
var button = document.getElementById("theme-button");
if (button) {
    button.addEventListener('click', switchTheme);
}

// Footnote popup functionality
(function() {
    function initFootnotes() {
        var footnoteRefs = document.querySelectorAll('a.footnote-ref');
        var popup = null;
        var hideTimer = null;

        function scheduleHide() {
            hideTimer = setTimeout(function() {
                if (popup && popup.parentNode) {
                    popup.parentNode.removeChild(popup);
                    popup = null;
                }
            }, 100);
        }

        function cancelHide() {
            if (hideTimer) {
                clearTimeout(hideTimer);
                hideTimer = null;
            }
        }

        footnoteRefs.forEach(function(ref) {
            ref.addEventListener('mouseenter', function(e) {
                cancelHide();

                // Remove any existing popup
                if (popup && popup.parentNode) {
                    popup.parentNode.removeChild(popup);
                    popup = null;
                }

                var footnoteId = ref.getAttribute('href').substring(1);
                var footnoteContent = document.getElementById(footnoteId);

                if (footnoteContent) {
                    // Create popup
                    popup = document.createElement('div');
                    popup.className = 'footnote-popup';

                    // Clone the content but remove the back link
                    var content = footnoteContent.cloneNode(true);
                    var backLink = content.querySelector('.footnote-back');
                    if (backLink && backLink.parentNode) {
                        backLink.parentNode.removeChild(backLink);
                    }

                    // Use innerHTML to preserve links and formatting
                    popup.innerHTML = content.innerHTML.trim();

                    // Position popup
                    var rect = ref.getBoundingClientRect();
                    popup.style.position = 'absolute';
                    popup.style.left = rect.left + window.pageXOffset + 'px';
                    popup.style.top = (rect.bottom + window.pageYOffset + 5) + 'px';

                    popup.addEventListener('mouseenter', cancelHide);
                    popup.addEventListener('mouseleave', scheduleHide);

                    document.body.appendChild(popup);
                }
            });

            ref.addEventListener('mouseleave', scheduleHide);
        });
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', initFootnotes);
    } else {
        initFootnotes();
    }
})();
