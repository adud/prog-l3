

<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">








<html xmlns="http://www.w3.org/1999/xhtml" lang="en">
	<head>
	    <title>CAS &#8211; Central Authentication Service</title>
        
		
        <link type="text/css" rel="stylesheet" href="/cas/themes/ensl-standard/cas.css;jsessionid=2E77890550200AE4CE08E3B8CBA41E24" />
        <meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
	    <link rel="icon" href="/cas/favicon.ico;jsessionid=2E77890550200AE4CE08E3B8CBA41E24" type="image/x-icon" />
	</head>
	<body id="cas" class="fl-theme-iphone">
   <!-- 
       <div class="flc-screenNavigator-view-container">
        <div class="fl-screenNavigator-view">
            <div id="header" class="flc-screenNavigator-navbar fl-navbar fl-table">
				<h1 id="company-name">Jasig</h1>
                <h1 id="app-name" class="fl-table-cell">Central Authentication Service (CAS)</h1>
            </div>		
            <div id="content" class="fl-screenNavigator-scroll-container">
    -->
    	<div id="content">
        




  <!-- 
  		<div class="box fl-panel" id="login">
  -->
  <form id="fm1" class="fm-v clearfix" action="/cas/login;jsessionid=2E77890550200AE4CE08E3B8CBA41E24?service=https%3A%2F%2Fperso.ens-lyon.fr%2Fphilippe.audebaud%2Fdl%2FThPr%2FExercices%2Ftp4.v" method="post">
                  
                <!-- Congratulations on bringing CAS online!  The default authentication handler authenticates where usernames equal passwords: go ahead, try it out. -->
                <!--     <h2>Enter your Username and Password</h2>-->
  		<div id="login" class="box">
  			<div id="bandeau">
                <a target="_blank" href="http://www.ens-lyon.fr">
                  <img height="113" width="614" border="0" align="left" alt="logo de l'Ecole Normale Supérieure de Lyon" src="themes/ensl-standard/images/bandeau-CAS.jpg"/>
                </a>
            </div>
<!--             <div style="clear:both;display: inline-block; margin-left: 60px; margin-top:15px; margin-bottom:30px;position:relative;">

                <font face="verdana,arial,sans-serif" size="5" color="#000000">
                Service Central d'Authentification
                </font>
            </div>
-->
            <div id="intro">
                <p align="justify">
                <font face="verdana,arial,sans-serif" size="2">
                Le service auquel vous souhaitez acc&eacute;der n&eacute;cessite une authentification.<br/><br/>
                Pour vous connecter, utilisez le compte informatique fourni par l'ENS de Lyon ou la Biblioth&egrave;que Diderot de Lyon (login et mot de passe).
                </font>
                </p>
            </div>
            
			
             <div style="clear:both; text-align:right; margin-bottom:40px; margin-right:60px;">
                    <!-- <div class="row fl-controls-left">-->
                        <label for="username" class="fl-label"><span class="accesskey">U</span>sername:</label>
						

						
						
						<input id="username" name="username" class="required" tabindex="1" accesskey="u" type="text" value="" size="25" autocomplete="false"/>
						
						<br/>
                   <!--  </div>
                    <div class="row fl-controls-left"> -->
                        <label for="password" class="fl-label"><span class="accesskey">P</span>assword:</label>
						
						
						<input id="password" name="password" class="required" tabindex="2" accesskey="p" type="password" value="" size="25" autocomplete="off"/>
                   <!--  </div>
                    <div class="row check">-->
                  		<br/>
                        <input id="warn" name="warn" value="true" tabindex="3" accesskey="w" type="checkbox" />
                        <label for="warn"><span class="accesskey">W</span>arn me before logging me into other sites.</label>
                        <br/>
                   <!--  </div>
                    <div class="row btn-row">-->
                    <div style="clear:both;">
						<input type="hidden" name="lt" value="LT-1840170-VDMa67GRaqpbfgCGsTuNwZjGtZnl6n" />
						<input type="hidden" name="execution" value="e1s1" />
						<input type="hidden" name="_eventId" value="submit" />

                        <input name="submit" accesskey="l" value="LOGIN" tabindex="4" type="submit" />
                        <input name="reset" accesskey="c" value="CLEAR" tabindex="5" type="reset" />
                    </div>
                    <div id='message_username' style="float: right;">
              			<span style="color: red; font-size: 2em;"></span>
            		</div>
				</div>
            
            <div id="secu" style="clear:both; margin:30px;">
        		<font face="verdana,arial,sans-serif" size="2" color="#666666">
        			<b>Pour des raisons de sécurité, fermez votre navigateur web après avoir accédé aux services protégés !
        			<br/><br/>
        		
            <a href="http://www.ens-lyon.fr/sites/default/files/2017-09/charte2016-final-correction24102016.pdf">Nouvelle charte 2016</a> L'utilisation de l'ensemble des ressources informatiques et numériques de l'établissement est soumise à l'acceptation de la <a href="http://www.ens-lyon.fr/sites/default/files/2017-09/charte2016-final-correction24102016.pdf">charte informatique</a>.


              <br/>                                                                     <br/>
<a href="http://www.ens-lyon.fr/sites/default/files/2017-10/charte2016_final_en.pdf">New charter 2016</a> The use of all the IT and digital resources of the institution is subject to acceptance of the <a href="http://www.ens-lyon.fr/sites/default/files/2017-10/charte2016_final_en.pdf">IT charter</a>.


            
            	
        			</b>
        		</font>
        	</div>
            
            <div style="clear:both; margin-right:20px; margin-left:20px;margin-bottom:20px">
          		<p align="justify">
            		<font face="verdana,arial,sans-serif" size="1">
              			Méfiez-vous de tous les programmes et pages web qui vous demandent
              			de vous authentifier. Les pages sécurisées de l'ENS de Lyon demandant votre nom
              			d'utilisateur et votre de passe ont des URLs de la forme "https://xxx.ens-lyon.fr" ou "https://xxx.ens-lyon.eu" ou "https://xxx.bibliotheque-diderot.fr".
              			De plus, votre navigateur doit indiquer que vous accédez &agrave;  une page
              			sécurisée.
            		</font>
          		</p>
        	</div>

          </form>



</div>
<!-- 
                <div id="footer" class="fl-panel fl-note fl-bevel-white fl-font-size-80">
                	<a id="jasig" href="http://www.jasig.org" title="go to Jasig home page"></a>
                    <div id="copyright">
                        <p>Copyright &copy; 2005 - 2012 Jasig, Inc. All rights reserved.</p>
                        <p>Powered by <a href="http://www.jasig.org/cas">Jasig Central Authentication Service 3.5.2</a></p>
                    </div>
                </div>
            </div>
        </div>
-->
        <script type="text/javascript" src="https://ajax.googleapis.com/ajax/libs/jquery/1.4.2/jquery.min.js"></script>
        <script type="text/javascript" src="https://ajax.googleapis.com/ajax/libs/jqueryui/1.8.5/jquery-ui.min.js"></script>
        <script type="text/javascript" src="/cas/js/cas.js;jsessionid=2E77890550200AE4CE08E3B8CBA41E24"></script>
    </body>
</html>


